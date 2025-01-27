{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeFamilies #-}

module Cardano.Ledger.State.Query where

import qualified Cardano.Ledger.Alonzo.TxBody as Alonzo
import qualified Cardano.Ledger.Credential as Credential
import qualified Cardano.Ledger.Keys as Keys
import qualified Cardano.Ledger.Shelley.EpochBoundary as EpochBoundary
import qualified Cardano.Ledger.Shelley.LedgerState as Shelley
import qualified Cardano.Ledger.Shelley.UTxO as Shelley
import Cardano.Ledger.State.Orphans
import Cardano.Ledger.State.Schema
import Cardano.Ledger.State.Transform
import Cardano.Ledger.State.UTxO
import qualified Cardano.Ledger.TxIn as TxIn
import Conduit
import Control.Foldl (Fold (..))
import Control.Iterate.SetAlgebra
import Control.Monad
import Control.Monad.Trans.Reader
import qualified Data.Compact.KeyMap as KeyMap
import Data.Functor
import qualified Data.IntMap.Strict as IntMap
import qualified Data.Map.Strict as Map
import Data.Text as T
import Database.Persist.Sqlite

-- Populate database

insertGetKey ::
  ( MonadIO m,
    PersistUniqueWrite backend,
    PersistRecordBackend record backend,
    AtLeastOneUniqueKey record
  ) =>
  record ->
  ReaderT backend m (Key record)
insertGetKey = fmap (either entityKey id) . insertBy

insertUTxOState ::
  MonadIO m =>
  Shelley.UTxOState CurrentEra ->
  ReaderT SqlBackend m (Key UtxoState)
insertUTxOState Shelley.UTxOState {..} = do
  insert $
    UtxoState
      { utxoStateDeposited = _deposited,
        utxoStateFees = _fees,
        utxoStatePpups = _ppups
      }

insertUTxO ::
  MonadIO m =>
  Shelley.UTxO CurrentEra ->
  Key UtxoState ->
  ReaderT SqlBackend m ()
insertUTxO utxo stateKey = do
  mapM_ insertTxOut $ Map.toList (Shelley.unUTxO utxo)
  where
    insertTxOut (TxIn.TxIn txId txIx, out) = do
      txKey <-
        insert $ Tx {txInIx = fromIntegral txIx, txInId = txId, txOut = out}
      txsKey <-
        case toTxOut' mempty out of
          TxOutNoStake' out' -> do
            insert $
              Txs
                { txsInIx = fromIntegral txIx,
                  txsInId = txId,
                  txsOut = out',
                  txsStakeCredential = Nothing
                }
          TxOut' out' cred -> do
            credId <- insertGetKey (Credential (Keys.asWitness cred))
            insert $
              Txs
                { txsInIx = fromIntegral txIx,
                  txsInId = txId,
                  txsOut = out',
                  txsStakeCredential = Just credId
                }
      insert_ $
        UtxoEntry
          { utxoEntryTxId = txKey,
            utxoEntryTxsId = txsKey,
            utxoEntryStateId = stateKey
          }

insertDState :: MonadIO m => Shelley.DState C -> ReaderT SqlBackend m DStateId
insertDState Shelley.DState {..} = do
  let irDeltaReserves = Shelley.deltaReserves _irwd
  let irDeltaTreasury = Shelley.deltaTreasury _irwd
  dstateId <- insert $ DState (Enc _fGenDelegs) _genDelegs irDeltaReserves irDeltaTreasury
  forM_ (Map.toList _rewards) $ \(cred, c) -> do
    credId <- insertGetKey (Credential (Keys.asWitness cred))
    insert_ (Reward dstateId credId c)
  forM_ (Map.toList _delegations) $ \(cred, spKeyHash) -> do
    credId <- insertGetKey (Credential (Keys.asWitness cred))
    keyHashId <- insertGetKey (KeyHash (Keys.asWitness spKeyHash))
    insert_ (Delegation dstateId credId keyHashId)
  forM_ (Map.toList (biMapToMap _ptrs)) $ \(ptr, cred) -> do
    credId <- insertGetKey (Credential (Keys.asWitness cred))
    insert_ (Ptr dstateId credId ptr)
  forM_ (Map.toList (Shelley.iRReserves _irwd)) $ \(cred, c) -> do
    credId <- insertGetKey (Credential (Keys.asWitness cred))
    insert_ (IRReserves dstateId credId c)
  forM_ (Map.toList (Shelley.iRTreasury _irwd)) $ \(cred, c) -> do
    credId <- insertGetKey (Credential (Keys.asWitness cred))
    insert_ (IRTreasury dstateId credId c)
  pure dstateId

insertLedgerState ::
  MonadIO m => EpochStateId -> Shelley.LedgerState CurrentEra -> ReaderT SqlBackend m ()
insertLedgerState epochStateKey Shelley.LedgerState {..} = do
  stateKey <- insertUTxOState _utxoState
  insertUTxO (Shelley._utxo _utxoState) stateKey
  dstateKey <- insertDState $ Shelley._dstate _delegationState
  insert_
    LedgerState
      { ledgerStateUtxoId = stateKey,
        ledgerStateDstateId = dstateKey,
        ledgerStatePstateBin = Shelley._pstate _delegationState,
        ledgerStateEpochStateId = epochStateKey
      }

insertSnapShot ::
  MonadIO m =>
  Key EpochState ->
  SnapShotType ->
  EpochBoundary.SnapShot C ->
  ReaderT SqlBackend m ()
insertSnapShot snapShotEpochStateId snapShotType EpochBoundary.SnapShot {..} = do
  snapShotId <- insert $ SnapShot {snapShotType, snapShotEpochStateId}
  forM_ (Map.toList (EpochBoundary.unStake _stake)) $ \(cred, c) -> do
    credId <- insertGetKey (Credential (Keys.asWitness cred))
    insert_ (SnapShotStake snapShotId credId c)
  forM_ (Map.toList _delegations) $ \(cred, spKeyHash) -> do
    credId <- insertGetKey (Credential (Keys.asWitness cred))
    keyHashId <- insertGetKey (KeyHash (Keys.asWitness spKeyHash))
    insert_ (SnapShotDelegation snapShotId credId keyHashId)
  forM_ (Map.toList _poolParams) $ \(keyHash, pps) -> do
    keyHashId <- insertGetKey (KeyHash (Keys.asWitness keyHash))
    insert_ (SnapShotPool snapShotId keyHashId pps)

insertSnapShots ::
  MonadIO m =>
  Key EpochState ->
  EpochBoundary.SnapShots C ->
  ReaderT SqlBackend m ()
insertSnapShots epochStateKey EpochBoundary.SnapShots {..} = do
  mapM_
    (uncurry (insertSnapShot epochStateKey))
    [ (SnapShotMark, _pstakeMark),
      (SnapShotSet, _pstakeSet),
      (SnapShotGo, _pstakeGo)
    ]

insertEpochState ::
  MonadIO m => Shelley.EpochState CurrentEra -> ReaderT SqlBackend m ()
insertEpochState Shelley.EpochState {..} = do
  epochStateKey <-
    insert
      EpochState
        { epochStateTreasury = Shelley._treasury esAccountState,
          epochStateReserves = Shelley._reserves esAccountState,
          epochStatePrevPp = esPrevPp,
          epochStatePp = esPp,
          epochStateNonMyopic = esNonMyopic,
          epochStateSnapShotsFee = EpochBoundary._feeSS esSnapshots
        }
  insertSnapShots epochStateKey esSnapshots
  insertLedgerState epochStateKey esLState

-- Query database

selectMap ::
  ( MonadResource m,
    Ord k,
    PersistEntity record,
    PersistEntityBackend record ~ SqlBackend
  ) =>
  [Filter record] ->
  (record -> ReaderT SqlBackend m (k, a)) ->
  ReaderT SqlBackend m (Map.Map k a)
selectMap fs f =
  runConduit $
    selectSource fs [] .| mapMC (\(Entity _ a) -> f a)
      .| foldlC (\m (k, v) -> Map.insert k v m) mempty

getSnapShotNoSharing ::
  MonadResource m =>
  Key EpochState ->
  SnapShotType ->
  ReaderT SqlBackend m (EpochBoundary.SnapShot C)
getSnapShotNoSharing epochStateId snapShotType = do
  snapShotId <-
    selectFirst
      [SnapShotType ==. snapShotType, SnapShotEpochStateId ==. epochStateId]
      []
      <&> \case
        Nothing -> error $ "Missing a snapshot: " ++ show snapShotType
        Just (Entity snapShotId _) -> snapShotId
  stake <-
    selectMap [SnapShotStakeSnapShotId ==. snapShotId] $ \SnapShotStake {..} -> do
      Credential credential <- getJust snapShotStakeCredentialId
      pure (Keys.coerceKeyRole credential, snapShotStakeCoin)
  delegations <-
    selectMap [SnapShotDelegationSnapShotId ==. snapShotId] $ \SnapShotDelegation {..} -> do
      Credential credential <- getJust snapShotDelegationCredentialId
      KeyHash keyHash <- getJust snapShotDelegationKeyHash
      --TODO ^ rename snapShotDelegationKeyHashId
      pure (Keys.coerceKeyRole credential, Keys.coerceKeyRole keyHash)
  poolParams <-
    selectMap [SnapShotPoolSnapShotId ==. snapShotId] $ \SnapShotPool {..} -> do
      KeyHash keyHash <- getJust snapShotPoolKeyHashId
      pure (Keys.coerceKeyRole keyHash, snapShotPoolParams)
  pure
    EpochBoundary.SnapShot
      { _stake = EpochBoundary.Stake stake,
        _delegations = delegations,
        _poolParams = poolParams
      }

getSnapShotsNoSharing ::
  MonadResource m =>
  Entity EpochState ->
  ReaderT SqlBackend m (EpochBoundary.SnapShots C)
getSnapShotsNoSharing (Entity epochStateId EpochState {epochStateSnapShotsFee}) = do
  mark <- getSnapShotNoSharing epochStateId SnapShotMark
  set <- getSnapShotNoSharing epochStateId SnapShotSet
  go <- getSnapShotNoSharing epochStateId SnapShotGo
  pure $
    EpochBoundary.SnapShots
      { _pstakeMark = mark,
        _pstakeSet = set,
        _pstakeGo = go,
        _feeSS = epochStateSnapShotsFee
      }

getSnapShotWithSharing ::
  MonadResource m =>
  [EpochBoundary.SnapShot C] ->
  Key EpochState ->
  SnapShotType ->
  ReaderT SqlBackend m (EpochBoundary.SnapShot C)
getSnapShotWithSharing otherSnapShots epochStateId snapShotType = do
  let otherStakes =
        EpochBoundary.unStake . EpochBoundary._stake <$> otherSnapShots
  let otherPoolParams = EpochBoundary._poolParams <$> otherSnapShots
  let otherDelegations = EpochBoundary._delegations <$> otherSnapShots
  snapShotId <-
    selectFirst
      [SnapShotType ==. snapShotType, SnapShotEpochStateId ==. epochStateId]
      []
      <&> \case
        Nothing -> error $ "Missing a snapshot: " ++ show snapShotType
        Just (Entity snapShotId _) -> snapShotId
  stake <-
    selectMap [SnapShotStakeSnapShotId ==. snapShotId] $ \SnapShotStake {..} -> do
      Credential credential <- getJust snapShotStakeCredentialId
      pure
        (interns (Keys.coerceKeyRole credential) otherStakes, snapShotStakeCoin)
  poolParams <-
    selectMap [SnapShotPoolSnapShotId ==. snapShotId] $ \SnapShotPool {..} -> do
      KeyHash keyHash <- getJust snapShotPoolKeyHashId
      pure
        ( interns (Keys.coerceKeyRole keyHash) otherPoolParams,
          snapShotPoolParams
        )
  delegations <-
    selectMap [SnapShotDelegationSnapShotId ==. snapShotId] $ \SnapShotDelegation {..} -> do
      Credential credential <- getJust snapShotDelegationCredentialId
      KeyHash keyHash <- getJust snapShotDelegationKeyHash
      pure
        ( interns (Keys.coerceKeyRole credential) otherDelegations,
          intern (Keys.coerceKeyRole keyHash) poolParams
        )
  pure
    EpochBoundary.SnapShot
      { _stake = EpochBoundary.Stake stake,
        _delegations = delegations,
        _poolParams = poolParams
      }

getSnapShotsWithSharing ::
  MonadResource m =>
  Entity EpochState ->
  ReaderT SqlBackend m (EpochBoundary.SnapShots C)
getSnapShotsWithSharing (Entity epochStateId EpochState {epochStateSnapShotsFee}) = do
  mark <- getSnapShotWithSharing [] epochStateId SnapShotMark
  set <- getSnapShotWithSharing [mark] epochStateId SnapShotSet
  go <- getSnapShotWithSharing [mark, set] epochStateId SnapShotGo
  pure $
    EpochBoundary.SnapShots
      { _pstakeMark = mark,
        _pstakeSet = set,
        _pstakeGo = go,
        _feeSS = epochStateSnapShotsFee
      }

sourceUTxO ::
  MonadResource m =>
  ConduitM () (TxIn.TxIn C, Alonzo.TxOut CurrentEra) (ReaderT SqlBackend m) ()
sourceUTxO =
  selectSource [] []
    .| mapC (\(Entity _ Tx {..}) -> (TxIn.TxIn txInId (fromIntegral txInIx), txOut))

sourceUTxOs ::
  MonadResource m =>
  Map.Map (Credential.StakeCredential C) a ->
  ConduitM () (TxIn.TxIn C, TxOut') (ReaderT SqlBackend m) ()
sourceUTxOs stakeCredentials =
  selectSource [] []
    .| mapMC
      ( \(Entity _ Txs {..}) -> do
          let txi = TxIn.TxIn txsInId (fromIntegral txsInIx)
          case txsStakeCredential of
            Nothing -> pure (txi, TxOutNoStake' txsOut)
            Just credId -> do
              Credential credential <- getJust credId
              let !sharedCredential = intern (Keys.coerceKeyRole credential) stakeCredentials
              pure (txi, TxOut' txsOut sharedCredential)
      )

foldDbUTxO ::
  MonadUnliftIO m =>
  -- | Folding function
  (a -> (TxIn.TxIn C, Alonzo.TxOut CurrentEra) -> a) ->
  -- | Empty acc
  a ->
  -- | Path to Sqlite db
  Text ->
  m a
foldDbUTxO f m fp = runSqlite fp (runConduit (sourceUTxO .| foldlC f m))

-- sourceUTxOr ::
--      MonadResource m
--   => Int64 -> Int64 -> ConduitM () (TxIn.TxIn C, Alonzo.TxOut CurrentEra) (ReaderT SqlBackend m) ()
-- sourceUTxOr b t =
--   selectSource [TxId >. TxKey (SqlBackendKey b) , TxId <. TxKey (SqlBackendKey t)] [] .|
--   mapC (\(Entity _ Tx {..}) -> (TxIn.TxIn txInId (fromIntegral txInIx), txOut))

-- foldDbUTxOr ::
--      MonadUnliftIO m
--   => Int64
--   -> Int64
--   -> (a -> (TxIn.TxIn C, Alonzo.TxOut CurrentEra) -> a) -- ^ Folding function
--   -> a -- ^ Empty acc
--   -> Text -- ^ Path to Sqlite db
--   -> m a
-- foldDbUTxOr b t f m fp = runSqlite fp (runConduit (sourceUTxOr b t .| foldlC f m))

lsId :: Key LedgerState
lsId = LedgerStateKey (SqlBackendKey 1)

getLedgerState ::
  MonadIO m =>
  Shelley.UTxO CurrentEra ->
  LedgerState ->
  Shelley.DState C ->
  ReaderT SqlBackend m (Shelley.LedgerState CurrentEra)
getLedgerState utxo LedgerState {..} dstate = do
  UtxoState {..} <- getJust ledgerStateUtxoId
  pure
    Shelley.LedgerState
      { Shelley._utxoState =
          Shelley.UTxOState
            { Shelley._utxo = utxo,
              Shelley._deposited = utxoStateDeposited,
              Shelley._fees = utxoStateFees,
              Shelley._ppups = utxoStatePpups
            },
        Shelley._delegationState =
          Shelley.DPState
            { Shelley._dstate = dstate,
              Shelley._pstate = ledgerStatePstateBin
            }
      }

getDStateNoSharing ::
  MonadIO m => Key DState -> ReaderT SqlBackend m (Shelley.DState C)
getDStateNoSharing dstateId = do
  DState {..} <- getJust dstateId
  rewards <-
    Map.fromList <$> do
      rws <- selectList [RewardDstateId ==. dstateId] []
      forM rws $ \(Entity _ Reward {..}) -> do
        Credential credential <- getJust rewardCredentialId
        pure (Keys.coerceKeyRole credential, rewardCoin)
  delegations <-
    Map.fromList <$> do
      ds <- selectList [DelegationDstateId ==. dstateId] []
      forM ds $ \(Entity _ Delegation {..}) -> do
        Credential credential <- getJust delegationCredentialId
        KeyHash keyHash <- getJust delegationStakePoolId
        pure (Keys.coerceKeyRole credential, Keys.coerceKeyRole keyHash)
  ptrs <-
    biMapFromList const <$> do
      ps <- selectList [PtrDstateId ==. dstateId] []
      forM ps $ \(Entity _ Ptr {..}) -> do
        Credential credential <- getJust ptrCredentialId
        pure (ptrPtr, Keys.coerceKeyRole credential)
  iRReserves <-
    Map.fromList <$> do
      ds <- selectList [IRReservesDstateId ==. dstateId] []
      forM ds $ \(Entity _ IRReserves {..}) -> do
        Credential credential <- getJust iRReservesCredentialId
        pure (Keys.coerceKeyRole credential, iRReservesCoin)
  iRTreasury <-
    Map.fromList <$> do
      ds <- selectList [IRTreasuryDstateId ==. dstateId] []
      forM ds $ \(Entity _ IRTreasury {..}) -> do
        Credential credential <- getJust iRTreasuryCredentialId
        pure (Keys.coerceKeyRole credential, iRTreasuryCoin)
  pure
    Shelley.DState
      { _rewards = rewards,
        _delegations = delegations,
        _ptrs = ptrs,
        _fGenDelegs = unEnc dStateFGenDelegs,
        _genDelegs = dStateGenDelegs,
        _irwd =
          Shelley.InstantaneousRewards
            { iRReserves = iRReserves,
              iRTreasury = iRTreasury,
              deltaReserves = dStateIrDeltaReserves,
              deltaTreasury = dStateIrDeltaTreasury
            }
      }

getDStateWithSharing ::
  MonadIO m => Key DState -> ReaderT SqlBackend m (Shelley.DState C)
getDStateWithSharing dstateId = do
  DState {..} <- getJust dstateId
  rewards <-
    Map.fromList <$> do
      rws <- selectList [RewardDstateId ==. dstateId] []
      forM rws $ \(Entity _ Reward {..}) -> do
        Credential credential <- getJust rewardCredentialId
        pure (Keys.coerceKeyRole credential, rewardCoin)
  delegations <-
    Map.fromList <$> do
      ds <- selectList [DelegationDstateId ==. dstateId] []
      forM ds $ \(Entity _ Delegation {..}) -> do
        Credential credential <- getJust delegationCredentialId
        let !cred = intern (Keys.coerceKeyRole credential) rewards
        KeyHash keyHash <- getJust delegationStakePoolId
        pure (cred, Keys.coerceKeyRole keyHash)
  ptrs <-
    biMapFromList const <$> do
      ps <- selectList [PtrDstateId ==. dstateId] []
      forM ps $ \(Entity _ Ptr {..}) -> do
        Credential credential <- getJust ptrCredentialId
        let !cred = intern (Keys.coerceKeyRole credential) rewards
        pure (ptrPtr, cred)
  iRReserves <-
    Map.fromList <$> do
      ds <- selectList [IRReservesDstateId ==. dstateId] []
      forM ds $ \(Entity _ IRReserves {..}) -> do
        Credential credential <- getJust iRReservesCredentialId
        let !cred = intern (Keys.coerceKeyRole credential) rewards
        pure (cred, iRReservesCoin)
  iRTreasury <-
    Map.fromList <$> do
      ds <- selectList [IRTreasuryDstateId ==. dstateId] []
      forM ds $ \(Entity _ IRTreasury {..}) -> do
        Credential credential <- getJust iRTreasuryCredentialId
        let !cred = intern (Keys.coerceKeyRole credential) rewards
        pure (cred, iRTreasuryCoin)
  pure
    Shelley.DState
      { _rewards = rewards,
        _delegations = delegations,
        _ptrs = ptrs,
        _fGenDelegs = unEnc dStateFGenDelegs,
        _genDelegs = dStateGenDelegs,
        _irwd =
          Shelley.InstantaneousRewards
            { iRReserves = iRReserves,
              iRTreasury = iRTreasury,
              deltaReserves = dStateIrDeltaReserves,
              deltaTreasury = dStateIrDeltaTreasury
            }
      }

loadDStateNoSharing :: MonadUnliftIO m => Text -> m (Shelley.DState C)
loadDStateNoSharing fp =
  runSqlite fp $ getDStateNoSharing (DStateKey (SqlBackendKey 1))

loadUTxONoSharing ::
  MonadUnliftIO m => Text -> m (Shelley.UTxO CurrentEra)
loadUTxONoSharing fp =
  runSqlite fp (Shelley.UTxO <$> runConduitFold sourceUTxO noSharing)

getLedgerStateNoSharing ::
  MonadUnliftIO m => Text -> m (Shelley.LedgerState CurrentEra)
getLedgerStateNoSharing fp =
  runSqlite fp $ do
    ledgerState@LedgerState {..} <- getJust lsId
    dstate <- getDStateNoSharing ledgerStateDstateId
    m <- runConduitFold sourceUTxO noSharing
    getLedgerState (Shelley.UTxO m) ledgerState dstate

getLedgerStateDStateSharing ::
  MonadUnliftIO m => Text -> m (Shelley.LedgerState CurrentEra)
getLedgerStateDStateSharing fp =
  runSqlite fp $ do
    ledgerState@LedgerState {..} <- getJust lsId
    dstate <- getDStateWithSharing ledgerStateDstateId
    m <- runConduitFold sourceUTxO noSharing
    getLedgerState (Shelley.UTxO m) ledgerState dstate

getLedgerStateDStateTxIxSharing ::
  MonadUnliftIO m =>
  Text ->
  m
    ( Shelley.LedgerState CurrentEra,
      IntMap.IntMap (Map.Map (TxIn.TxId C) (Alonzo.TxOut CurrentEra))
    )
getLedgerStateDStateTxIxSharing fp =
  runSqlite fp $ do
    ledgerState@LedgerState {..} <- getJust lsId
    dstate <- getDStateWithSharing ledgerStateDstateId
    ls <- getLedgerState (Shelley.UTxO mempty) ledgerState dstate
    m <- runConduitFold sourceUTxO txIxSharing
    pure (ls, m)

getLedgerStateDStateTxIxSharingKeyMap ::
  MonadUnliftIO m =>
  Text ->
  m
    ( Shelley.LedgerState CurrentEra,
      IntMap.IntMap (KeyMap.KeyMap (Alonzo.TxOut CurrentEra))
    )
getLedgerStateDStateTxIxSharingKeyMap fp =
  runSqlite fp $ do
    ledgerState@LedgerState {..} <- getJust lsId
    dstate <- getDStateWithSharing ledgerStateDstateId
    m <- runConduitFold sourceUTxO txIxSharingKeyMap
    ls <- getLedgerState (Shelley.UTxO mempty) ledgerState dstate
    pure (ls, m)

getLedgerStateDStateTxIdSharingKeyMap ::
  MonadUnliftIO m =>
  Text ->
  m
    ( Shelley.LedgerState CurrentEra,
      KeyMap.KeyMap (IntMap.IntMap (Alonzo.TxOut CurrentEra))
    )
getLedgerStateDStateTxIdSharingKeyMap fp =
  runSqlite fp $ do
    ledgerState@LedgerState {..} <- getJust lsId
    dstate <- getDStateWithSharing ledgerStateDstateId
    m <- runConduitFold sourceUTxO txIdSharingKeyMap
    ls <- getLedgerState (Shelley.UTxO mempty) ledgerState dstate
    pure (ls, m)

-- storeLedgerState ::
--      MonadUnliftIO m => Text -> Shelley.LedgerState CurrentEra -> m ()
-- storeLedgerState fp ls =
--   runSqlite fp $ do
--     runMigration migrateAll
--     insertLedgerState ls

storeEpochState ::
  MonadUnliftIO m => Text -> Shelley.EpochState CurrentEra -> m ()
storeEpochState fp es =
  runSqlite fp $ do
    runMigration migrateAll
    insertEpochState es

loadDbUTxO :: UTxOFold a -> Text -> IO a
loadDbUTxO (Fold f e g) fp = runSqlite fp (g <$> runConduit (sourceUTxO .| foldlC f e))

esId :: Key EpochState
esId = EpochStateKey (SqlBackendKey 1)

loadEpochStateEntity :: MonadUnliftIO m => Text -> m (Entity EpochState)
loadEpochStateEntity fp = runSqlite fp (getJustEntity esId)

loadSnapShotsNoSharing ::
  MonadUnliftIO m => Text -> Entity EpochState -> m (EpochBoundary.SnapShots C)
loadSnapShotsNoSharing fp = runSqlite fp . getSnapShotsNoSharing

loadSnapShotsWithSharing ::
  MonadUnliftIO m => Text -> Entity EpochState -> m (EpochBoundary.SnapShots C)
loadSnapShotsWithSharing fp = runSqlite fp . getSnapShotsWithSharing

-- getLedgerStateWithSharing ::
--      MonadUnliftIO m
--   => Text
--   -> m (Shelley.LedgerState CurrentEra, IntMap.IntMap (Map.Map (TxIn.TxId C) TxOut'))
-- getLedgerStateWithSharing fp =
--   runSqlite fp $ do
--     ledgerState@LedgerState {..} <- getJust lsId
--     dstate <- getDStateWithSharing ledgerStateDstateId
--     let stakeCredentials = Shelley._rewards dstate
--     ls <- getLedgerState (Shelley.UTxO mempty) ledgerState dstate
--     m <- runConduitFold (sourceUTxOs stakeCredentials) txIxSharing
--     pure (ls, m)

-- getLedgerStateDStateTxOutSharing ::
--      MonadUnliftIO m
--   => Text
--   -> m (Shelley.LedgerState CurrentEra, Map.Map (TxIn.TxIn C) TxOut')
-- getLedgerStateDStateTxOutSharing fp =
--   runSqlite fp $ do
--     ledgerState@LedgerState {..} <- getJust lsId
--     dstate <- getDStateWithSharing ledgerStateDstateId
--     let stakeCredentials = Shelley._rewards dstate
--     ls <- getLedgerState (Shelley.UTxO mempty) ledgerState dstate
--     m <- runConduitFold (sourceUTxOs stakeCredentials) noSharing
--     pure (ls, m)

-- getLedgerStateTxOutSharing ::
--      MonadUnliftIO m
--   => Text
--   -> m (Shelley.LedgerState CurrentEra, Map.Map (TxIn.TxIn C) TxOut')
-- getLedgerStateTxOutSharing fp =
--   runSqlite fp $ do
--     ledgerState@LedgerState {..} <- getJust lsId
--     dstate <- getDStateNoSharing ledgerStateDstateId
--     let stakeCredentials = Shelley._rewards dstate
--     ls <- getLedgerState (Shelley.UTxO mempty) ledgerState dstate
--     m <- runConduitFold (sourceUTxOs stakeCredentials) noSharing
--     pure (ls, m)

-- getLedgerStateWithSharingKeyMap ::
--      MonadUnliftIO m
--   => Text
--   -> m (Shelley.LedgerState CurrentEra, IntMap.IntMap (KeyMap.KeyMap TxOut'))
-- getLedgerStateWithSharingKeyMap fp =
--   runSqlite fp $ do
--     ledgerState@LedgerState {..} <- getJust lsId
--     dstate <- getDStateWithSharing ledgerStateDstateId
--     let stakeCredentials = Shelley._rewards dstate
--     ls <- getLedgerState (Shelley.UTxO mempty) ledgerState dstate
--     m <- runConduitFold (sourceUTxOs stakeCredentials) txIxSharingKeyMap
--     pure (ls, m)
