{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE NumDecimals #-}
{-# LANGUAGE NumericUnderscores #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Test.Cardano.Ledger.DependGraph where

import Cardano.Ledger.BaseTypes (Globals, boundRational, epochInfo)
import Cardano.Ledger.Coin
import qualified Cardano.Ledger.Val as Val
import Cardano.Slotting.EpochInfo.API (epochInfoSize)
import Cardano.Slotting.Slot (EpochNo (..), EpochSize (..), SlotNo (..))
import Control.Arrow ((&&&))
import Control.Lens hiding (elements)
import Control.Monad
import Control.Monad.Reader
import qualified Control.Monad.State.Lazy as State
import Control.Monad.Supply
import Control.Monad.Writer.Strict
import qualified Control.Monad.Writer.Strict as Writer
import Data.Bool (bool)
import Data.Either
import Data.Foldable
import qualified Data.Graph.Inductive as FGL
import Data.Group
import Data.HKD
import Data.List.NonEmpty (NonEmpty)
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Map.Merge.Strict as Map
import Data.Maybe (fromJust, mapMaybe)
import Data.Proxy
import Data.Ratio ((%))
import Data.Semigroup.Foldable (fold1)
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Traversable
import Data.Void
import GHC.Generics
import qualified PlutusTx
import QuickCheck.GenT
import qualified System.Random
import Test.Cardano.Ledger.ModelChain
import Test.Cardano.Ledger.ModelChain.Address
import Test.Cardano.Ledger.ModelChain.FeatureSet
import Test.Cardano.Ledger.ModelChain.Value

data GenActionContextF f = GenActionContext
  { _genActionContexts_epochs :: f EpochNo,
    _genActionContexts_genesesAcct :: f Coin,
    _genActionContexts_numGenesesAcct :: f Int,
    _genActionContexts_txnsPerSlot :: f Int,
    _genActionContexts_numSlotsUsed :: f Int, -- TODO: make this a fraction of slots used.
    _genActionContexts_numTxInputs :: f Int,
    _genActionContexts_numDCerts :: f Int
  }
  deriving (Generic)

instance FFunctor GenActionContextF where ffmap = ffmapDefault

instance FZip GenActionContextF where fzipWith = gfzipWith

instance FRepeat GenActionContextF where frepeat = gfrepeat

instance FFoldable GenActionContextF where ffoldMap = ffoldMapDefault

instance FTraversable GenActionContextF where ftraverse = gftraverse

type GenActionContext = GenActionContextF Gen

defaultGenActionContext :: GenActionContext
defaultGenActionContext =
  GenActionContext
    { _genActionContexts_epochs = choose (20, 30),
      _genActionContexts_genesesAcct = Coin <$> choose (100_000 * minOutput, 45e12),
      _genActionContexts_numGenesesAcct = choose (1, 20),
      _genActionContexts_txnsPerSlot = choose (1, 20),
      _genActionContexts_numSlotsUsed = choose (0, 100),
      _genActionContexts_numTxInputs = frequency [(10, pure 1), (1, choose (1, 8))],
      _genActionContexts_numDCerts = frequency [(10, pure 0), (1, choose (1, 5))]
    }

type GenModelM st era m =
  ( MonadReader (Globals, GenActionContext) m,
    State.MonadState st m,
    HasModelLedger era st,
    MonadGen m,
    KnownRequiredFeatures era,
    MonadSupply Integer m
  )

genInputs :: GenModelM st era m => m (Map ModelUTxOId (ModelTxOut era))
genInputs = do
  utxos0 <- shuffle =<< uses (modelLedger . modelLedger_utxos) (Map.toList . _modelUtxoMap_utxos)

  let spendable :: (Coin, ModelTxOut era) -> Coin
      spendable = fst

      go :: [(ModelUTxOId, (Coin, ModelTxOut era))] -> Coin -> [(ModelUTxOId, (Coin, ModelTxOut era))] -> [(ModelUTxOId, (Coin, ModelTxOut era))]
      go [] val acc
        | val >= Coin (minFee + minOutput) = acc
        | otherwise = error "insufficient UTxO's to proceed with generation."
      -- TODO, get rewards/fees back into circulation in generator.
      go (utxo : rest) val acc
        | val < Coin (minFee + minOutput) = go rest (val <> spendable (snd utxo)) (utxo : acc)
        | otherwise = acc

  numTxInputs <- liftGen =<< asks (_genActionContexts_numTxInputs . snd)
  let utxos1 = (take numTxInputs utxos0)
      val1 = foldMap (spendable . snd) utxos1
  pure $ Map.fromList $ (fmap . fmap) snd $ go (drop numTxInputs utxos0) val1 utxos1

-- | divide a value into several "chunks"
-- y = unfoldModelValue minCoin x
-- PREC: minCoin =< coin x
-- POSTC: fold y === x .&&. all ((minCoin =<) . coin) y
unfoldModelValue :: forall x. Ord x => Coin -> ModelValueSimple x -> Gen (NonEmpty (ModelValueSimple x))
unfoldModelValue (Coin minValue) = go
  where
    splitMA :: Sum Integer -> Gen (Sum Integer)
    splitMA (Sum a) =
      frequency
        [ (1, pure (Sum a)),
          (1, Sum <$> choose (0, a)),
          (1, pure (mempty))
        ]

    go :: ModelValueSimple x -> Gen (NonEmpty (ModelValueSimple x))
    go m@(ModelValueSimple (Coin ada, ma))
      | ada <= 2 * minValue = pure (pure m)
      | otherwise = do
        adaL <- Coin <$> choose (minValue, ada - minValue)
        maL <- traverseGrpMap splitMA ma
        let adaR = Coin ada ~~ adaL
            maR = ma ~~ maL
            m' = (pure (ModelValueSimple (adaL, maL)) <> pure (ModelValueSimple (adaR, maR)))
        frequency
          [ (10, pure m'),
            (1, fold1 <$> traverse go m')
          ]

genScriptData :: forall sf. KnownScriptFeature sf => ModelAddress sf -> Gen (IfSupportsPlutus () (Maybe PlutusTx.Data) sf)
genScriptData addr = traverseSupportsPlutus id $
  ifSupportsPlutus (Proxy :: Proxy sf) () $ case addr of
    ModelAddress _ -> pure Nothing
    ModelScriptAddress _ -> Just . PlutusTx.I <$> arbitrary

genOutputs ::
  GenModelM st era m =>
  Map ModelUTxOId (ModelTxOut era) ->
  IfSupportsMint () (ModelValue (ValueFeature era) era) (ValueFeature era) ->
  m ([(ModelUTxOId, ModelTxOut era)], ModelValue 'ExpectAdaOnly era)
genOutputs ins mint = do
  -- by assumption, there are no rewards; since they would have been outputs to
  -- earlier transactions, and thus have different value now. thus the non-ada
  -- values are entirely known qty multi-asset outputs.
  let (ModelValueSimple (Coin inAda, ma)) = either (error . show) id $ evalModelValueSimple $ unModelValue $ fromSupportsMint (\() -> mempty) id mint <> foldMap _mtxo_value ins
  -- TODO: corner case, if the amount of inAda < minFee + minOutput && ma > 0;
  -- the inputs are unspendable, and the generator needs to abort.
  (fee, outVals) <-
    if
        | inAda < minFee -> error "input too small"
        | inAda < minFee + minOutput -> pure (inAda, [])
        | otherwise -> do
          fee <- choose (minFee, min (inAda - minOutput) maxFee)
          outVals <- liftGen $ unfoldModelValue (Coin minOutput) (ModelValueSimple (Coin inAda ~~ Coin fee, ma))
          pure (fee, toList outVals)

  delegates <-
    uses
      (modelLedger . modelLedger_stake . snapshotQueue_mark . modelSnapshot_delegations)
      Map.keys

  outs <- for outVals $ \outVal -> do
    ui <- freshUtxoId
    addr <-
      frequency
        [ (1, elements $ fmap _mtxo_address $ toList ins),
          (1, freshPaymentAddress "genOutputs"),
          (bool 1 0 (null delegates), elements delegates)
        ]
    dh <- liftGen $ genScriptData addr
    pure (ui, ModelTxOut addr (ModelValue $ mkModelValue outVal) dh)
  pure (outs, ModelValue $ ModelValue_Inject $ Coin $ fee)

genDCert :: forall st era m. GenModelM st era m => m (ModelDCert era)
genDCert = do
  stakeHolders <- uses (modelLedger . modelLedger_utxos) $ Map.keysSet . unGrpMap . _modelUtxoMap_balances
  registeredStake <- uses (modelLedger . modelLedger_stake . snapshotQueue_mark . modelSnapshot_stake) $ Map.keysSet
  pools <- uses (modelLedger . modelLedger_stake . snapshotQueue_mark . modelSnapshot_pools) $ Map.keys

  let unregisteredStake = Set.difference stakeHolders registeredStake

  frequency $
    [(1, ModelRegisterPool <$> genModelPool)]
      <> [ (1, ModelRegisterStake <$> elements (Set.toList unregisteredStake))
           | not (null unregisteredStake)
         ]
      <> [ (1, fmap ModelDelegate $ ModelDelegation <$> elements (Set.toList registeredStake) <*> elements pools)
           | not (null registeredStake),
             not (null pools)
         ]

genWdrl :: GenModelM st era m => m (Set (ModelAddress (ScriptFeature era)))
genWdrl = do
  allRewards <- use (modelLedger . modelLedger_rewards)
  rewards <- sublistOf $ Set.toList $ Map.keysSet $ unGrpMap allRewards
  pure $ Set.fromList rewards

genModelTx :: forall era m st. GenModelM st era m => m (ModelTx era)
genModelTx = do
  ins <- genInputs
  wdrl <- Map.fromSet (ModelValue . ModelValue_Var . ModelValue_Reward) <$> genWdrl

  mint <- pure $ ifSupportsMint (Proxy :: Proxy (ValueFeature era)) () mempty
  (outs, fee) <- genOutputs ins mint
  let txn =
        ModelTx
          { _mtxInputs = Map.keysSet ins,
            _mtxOutputs = outs,
            _mtxFee = fee <> fold wdrl, -- TODO, put withdwrawals in outputs sometimes.
            _mtxDCert = [],
            _mtxWdrl = wdrl,
            _mtxMint = mint,
            _mtxCollateral = ifSupportsPlutus (Proxy :: Proxy (ScriptFeature era)) () Set.empty
          }

  dcerts <- do
    st0 <- modelLedger <<%= applyModelTx txn
    numDCerts <- liftGen =<< asks (_genActionContexts_numDCerts . snd)
    txNo <- use (modelLedger . modelLedger_nextTxNo)
    dcerts <- replicateM numDCerts $ do
      dcert <- genDCert
      modelLedger %= applyModelDCert txNo dcert
      pure dcert

    modelLedger .= st0

    let removeDupDelegs seen = \case
          [] -> []
          dcert@(ModelDelegate (ModelDelegation x _)) : rest
            | Set.member x seen -> removeDupDelegs seen rest
            | otherwise -> dcert : removeDupDelegs (Set.insert x seen) rest
          dcert : rest -> dcert : removeDupDelegs seen rest
    pure $ removeDupDelegs Set.empty dcerts

  pure txn {_mtxDCert = dcerts}

genBlocksMade :: GenModelM st era m => m ModelBlocksMade
genBlocksMade = do
  pools <- use (modelLedger . modelLedger_stake . snapshotQueue_go . modelSnapshot_pools)
  currentEpoch <- use $ modelLedger . modelLedger_epoch
  EpochSize numSlots <- asks $ runIdentity . flip epochInfoSize currentEpoch . epochInfo . fst
  pools' <- Map.fromList . take (fromEnum numSlots) <$> shuffle (Map.toList pools)
  -- TODO: Model scenarios where pools make varying amounts of blocks (e.g. 0 or many)
  pure $ ModelBlocksMade $ 1 % max 1 (toInteger $ Map.size pools') <$ pools'

genModelEpoch :: GenModelM st era m => m (ModelEpoch era)
genModelEpoch = do
  currentEpoch <- use $ modelLedger . modelLedger_epoch
  EpochSize numSlots <- asks $ runIdentity . flip epochInfoSize currentEpoch . epochInfo . fst

  -- we don't have to put a block in every slot.
  numSlotsUsed <- liftGen =<< asks (_genActionContexts_numSlotsUsed . snd)

  slots <- take numSlotsUsed <$> sublistOf [0 .. numSlots -1]

  blocks <- for slots $ \slot' -> do
    numTxns <- liftGen =<< asks (_genActionContexts_txnsPerSlot . snd)
    txns <- replicateM numTxns $ do
      txn <- genModelTx
      modelLedger %= applyModelTx txn
      pure txn
    pure
      ModelBlock
        { _modelBlock_txSeq = txns,
          _modelBlock_slot = SlotNo slot'
        }

  blocksMade <- genBlocksMade
  modelLedger %= applyModelBlocksMade blocksMade

  pure
    ModelEpoch
      { _modelEpoch_blocks = blocks,
        _modelEpoch_blocksMade = blocksMade
      }

graphHeads :: FGL.Graph gr => gr a b -> [FGL.LNode a]
graphHeads gr = mapMaybe f (FGL.nodes gr)
  where
    f n = do
      c <- fst (FGL.match n gr)
      guard $ null $ FGL.inn' c
      pure $ FGL.labNode' c

-- TODO: this could be a more interesting pool.
genModelPool :: (Show n, MonadSupply n m) => m (ModelPoolParams era)
genModelPool = freshPoolAddress >>= genModelPool'

genModelPool' :: (Show n, MonadSupply n m) => ModelPoolId -> m (ModelPoolParams era)
genModelPool' pool = do
  racct <- freshRewardAddress
  powner <- freshRewardAddress
  pure $ ModelPoolParams pool (Coin 0) (Coin 0) (fromJust $ boundRational $ 0 % 1) racct [powner]

minFee :: Integer
minFee = 100000

maxFee :: Integer
maxFee = 10 * minFee

type ModelTxId = (EpochNo, SlotNo, Int) -- TODO, don't refer to modelTx's

-- TODO: monoidal-containers
newtype MonMap k v = MonMap {unMonMap :: Map k v}
  deriving (Functor)

instance (Ord k, Semigroup v) => Semigroup (MonMap k v) where
  MonMap xs <> MonMap ys = MonMap $ Map.unionWith (<>) xs ys

instance (Ord k, Semigroup v) => Monoid (MonMap k v) where
  mempty = MonMap Map.empty

genPartition :: [a] -> Gen ([a], [a])
genPartition xs = do
  size <- getSize
  let bias = frequency [(max 0 (100 - size), pure False), (max 0 size, pure True)]
  partitionEithers <$> traverse (\x -> bool (Left x) (Right x) <$> bias) xs

-- Postprocessing pass to fix annoying correctness issues.  If possible, each of
-- these fixes should be somehow incorporated into the generator itself.
--
-- 1. generator can produce too-small outputs.  fixed by adding some extra coin
-- to small outputs, spending the excess into fees, and propogating inputs
-- backwards using numerically lowest input.
-- 2. generator can produce multiple genesis accounts with same owner.  owners
-- are perturbed with model utxo id.
fixupDust ::
  forall era.
  Coin ->
  -- | min Utxo value
  ( [(ModelUTxOId, ModelAddress (ScriptFeature era), Coin)],
    [ModelEpoch era]
  ) ->
  ( [(ModelUTxOId, ModelAddress (ScriptFeature era), Coin)],
    [ModelEpoch era]
  )
fixupDust minOutput' (genesis0, epochs) =
  let genesis :: [(ModelUTxOId, ModelAddress (ScriptFeature era), Coin)]
      genesis =
        let dups = Writer.execWriter (State.evalStateT (traverse_ (\(_, ma, _) -> at ma <<.= Just () >>= traverse_ (const $ tell $ Set.singleton ma)) genesis0) Set.empty)
         in if Set.null dups
              then genesis0
              else
                error $
                  unlines
                    [ "duplicate genesis accounts:",
                      show dups,
                      show genesis0
                    ]

      txns :: Map ModelTxId (ModelTx era)
      txns =
        Map.fromList
          [ (((EpochNo $ fromIntegral epoch), (_modelBlock_slot block), txNum), tx)
            | (epoch, ModelEpoch blocks _) <- itoList epochs,
              block <- toList blocks,
              (txNum, tx) <- itoList $ _modelBlock_txSeq block
          ]

      -- absence of a utxo means it's from the genesis account.
      outUtxos :: Map ModelUTxOId ModelTxId
      outUtxos =
        Map.fromList $
          [ (ui, mtxId)
            | (mtxId, tx) <- Map.toList txns,
              ui <- toListOf (modelTx_outputs . traverse . _1) tx
          ]

      spendUtxos :: Map ModelUTxOId ModelTxId
      spendUtxos =
        Map.fromList $
          [ (ui, mtxId)
            | (mtxId, tx) <- Map.toList txns,
              ui <- toListOf (modelTx_inputs . folded) tx
          ]

      -- how much needs to be added to the UTXO to meet the minimum
      tooSmall :: Map ModelUTxOId Coin
      tooSmall =
        Map.fromList $
          [ (ui, delta)
            | (_, tx) <- Map.toList txns,
              (ui, txo) <- toListOf (modelTx_outputs . traverse) tx,
              delta <- case runIdentity $ evalModelValue (pure $ pure $ Coin 0) (unModelValue $ _mtxo_value txo) of
                Left _ -> []
                Right qty
                  | qty >= minOutput' -> []
                  | otherwise -> [minOutput' ~~ qty]
          ]

      genesisMap = Map.fromList $ (view _1 &&& view _3) <$> genesis

      txns', txns'' :: Map ModelTxId (ModelTx era)
      txns' = Map.merge Map.preserveMissing Map.dropMissing (Map.zipWithMatched $ \_ mtx val -> over modelTx_fee (offsetModelValue val) mtx) txns $ unMonMap $ foldMap (MonMap . uncurry Map.singleton) $ Map.intersectionWith (,) spendUtxos tooSmall

      offsetModelValue c (ModelValue x) = ModelValue (x `ModelValue_Add` ModelValue_Inject c)

      (txns'', genesis', _) =
        let popItem = do
              x <- use _3
              case Map.lookupMin x of
                Nothing -> pure Nothing
                Just (k, v) -> do
                  _3 . at k .= Nothing
                  pure $ Just (k, v)
            go =
              popItem >>= \case
                Nothing -> pure ()
                Just (k, v) -> do
                  -- fix the source of this UTxO to have enough available to create
                  -- it.
                  case Map.lookup k outUtxos of
                    Nothing -> do
                      -- utxo is a genesis account, it can be adjusted without any further work
                      _2 . at k <>= Just v
                    Just txid -> do
                      -- add the offset amount to the output
                      _1 . at txid . _Just . modelTx_outputAt k . _Just . modelTxOut_value %= offsetModelValue v
                      -- pick an input to add the balance to. queue it up.
                      preuse (_1 . ix txid . modelTx_inputs . folded) >>= \case
                        Nothing -> error "fixupDust: txn has no inputs"
                        Just k' -> _3 . at k' <>= Just v
                  go
         in State.execState go (txns', genesisMap, tooSmall)

      txns''unnest :: MonMap EpochNo (MonMap SlotNo (Map Int (ModelTx era)))
      txns''unnest = ifoldMap (\(epochNo, slotNo, txnNo) -> MonMap . Map.singleton epochNo . MonMap . Map.singleton slotNo . Map.singleton txnNo) txns''

      epochs' :: Map EpochNo [ModelBlock era]
      epochs' = fmap (fmap (\(slotNo, txnMap) -> ModelBlock slotNo $ fmap snd $ Map.toAscList txnMap) . Map.toAscList . unMonMap) $ unMonMap $ txns''unnest

      mapEpochs :: Int -> ModelEpoch era -> ModelEpoch era
      mapEpochs epochNo = set modelEpoch_blocks $ maybe [] id $ Map.lookup (EpochNo $ fromIntegral epochNo) epochs'
   in ( (\(ui, ma, val) -> (ui, ma, maybe val id $ Map.lookup ui genesis')) <$> genesis,
        imap mapEpochs epochs
      )

minOutput :: Integer
minOutput = 500_000

genGenesesUTxOs :: (MonadGen m, MonadSupply Integer m) => GenActionContext -> m [(ModelUTxOId, ModelAddress sf, Coin)]
genGenesesUTxOs ctx = do
  genesisSupply <- liftGen (_genActionContexts_genesesAcct ctx)
  g' <- liftGen $ unfoldModelValue @Void (Coin minOutput) (Val.inject genesisSupply)
  xs <- for g' $ \(ModelValueSimple (x, _)) ->
    (,,)
      <$> freshUtxoId
      <*> freshPaymentAddress "gen"
      <*> pure x

  pure $ toList xs

genModel ::
  forall era.
  KnownRequiredFeatures era =>
  Globals ->
  GenActionContext ->
  Gen
    ( [(ModelUTxOId, ModelAddress (ScriptFeature era), Coin)],
      [ModelEpoch era]
    )
genModel globals ctx = do
  let st0 :: Faucet (ModelLedger era)
      st0 = Faucet 0 $ mkModelLedger []

  model <- flip runReaderT (globals, ctx) $
    flip State.evalStateT st0 $ do
      genesisUtxos <- genGenesesUTxOs ctx
      modelLedger .= mkModelLedger genesisUtxos

      numEpochs <- liftGen $ _genActionContexts_epochs ctx
      epochs <- replicateM (fromEnum numEpochs) $ do
        epoch <- genModelEpoch
        pure epoch

      pure (genesisUtxos, epochs)

  pure model

-- TODO: is fixupDust actually ever useful/neccessary/fast?
-- pure $ fixupDust (Coin minOutput) model

freshUtxoId :: (Integral n, MonadSupply n m) => m ModelUTxOId
freshUtxoId = ModelUTxOId . toInteger <$> supply

freshPaymentAddress :: (Show n, MonadSupply n m) => String -> m (ModelAddress era)
freshPaymentAddress clue = ModelAddress . (("pay:" <> clue <> "_") <>) . show <$> supply

freshRewardAddress :: (Show n, MonadSupply n m) => m (ModelAddress era)
freshRewardAddress = ModelAddress . ("reward_" <>) . show <$> supply

freshPoolAddress :: (Show n, MonadSupply n m) => m ModelPoolId
freshPoolAddress = ModelPoolId . ("pool_" <>) . show <$> supply

-- TODO: handle this more elegantly
modelTxOut ::
  forall era.
  KnownScriptFeature (ScriptFeature era) =>
  (ModelAddress (ScriptFeature era)) ->
  (ModelValue (ValueFeature era) era) ->
  ModelTxOut era
modelTxOut x y =
  ModelTxOut x y $
    ifSupportsPlutus (Proxy @(ScriptFeature era)) () Nothing

-- Orphans
deriving newtype instance System.Random.Random EpochNo -- TODO: this can be moved closer to the package that defines EpochNo

instance MonadGen g => MonadGen (State.StateT s g) where
  liftGen = lift . liftGen
  variant n a = State.StateT $ \s -> variant n (State.runStateT a s)
  sized f = State.StateT $ \s -> sized (\i -> State.runStateT (f i) s)
  resize n a = State.StateT $ \s -> resize n (State.runStateT a s)
  choose = lift . choose

instance MonadGen g => MonadGen (ReaderT r g) where
  liftGen = lift . liftGen
  variant n a = ReaderT $ \s -> variant n (runReaderT a s)
  sized f = ReaderT $ \s -> sized (\i -> runReaderT (f i) s)
  resize n a = ReaderT $ \s -> resize n (runReaderT a s)
  choose = lift . choose

instance (Monoid w, MonadGen g) => MonadGen (WriterT w g) where
  liftGen = lift . liftGen
  variant n a = WriterT $ variant n (runWriterT a)
  sized f = WriterT $ sized (\i -> runWriterT (f i))
  resize n a = WriterT $ resize n (runWriterT a)
  choose = lift . choose

data Faucet a = Faucet
  { _faucet_supply :: !Integer,
    _faucet_state :: !a
  }

faucet_supply :: Lens' (Faucet a) Integer
faucet_supply a2fb s = (\b -> s {_faucet_supply = b}) <$> a2fb (_faucet_supply s)
{-# INLINE faucet_supply #-}

faucet_state :: Lens' (Faucet a) a
faucet_state a2fb s = (\b -> s {_faucet_state = b}) <$> a2fb (_faucet_state s)
{-# INLINE faucet_state #-}

instance HasModelLedger era a => HasModelLedger era (Faucet a) where
  modelLedger = faucet_state . modelLedger

instance {-# OVERLAPPING #-} (Monad m) => MonadSupply Integer (State.StateT (Faucet s) m) where
  supply = faucet_supply <<+= 1
  peek = use faucet_supply
  exhausted = pure False
