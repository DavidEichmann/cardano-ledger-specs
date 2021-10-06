{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NumDecimals #-}
{-# LANGUAGE NumericUnderscores #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Test.Cardano.Ledger.ModelChain.Properties where

import Cardano.Ledger.Alonzo (AlonzoEra)
import Cardano.Ledger.Alonzo.Scripts (ExUnits (..), Tag (..))
import qualified Cardano.Ledger.Alonzo.PParams as Alonzo
import Cardano.Ledger.BaseTypes (Globals (..), boundRational)
import Cardano.Ledger.Coin
import qualified Cardano.Ledger.Core as Core
import Cardano.Ledger.Keys (KeyRole (..))
import Cardano.Ledger.Mary.Value (AssetName (..))
import Cardano.Ledger.Shelley (ShelleyEra)
import Control.Arrow ((&&&))
import Control.DeepSeq
import Control.Lens
import Control.Monad (when)
import qualified Control.Monad.State.Strict as State
import qualified Control.Monad.Writer.Strict as Writer
import Control.State.Transition.Extended
import qualified Data.ByteString.Char8 as BS
import Data.Default.Class
import Data.Foldable
import Data.Functor.Contravariant (Predicate (..))
import Data.HKD
import qualified Data.List as List
import qualified Data.Map as Map
import Data.Maybe (fromJust, mapMaybe)
import Data.Monoid (Endo (..))
import Data.Ratio ((%))
import qualified Data.Set as Set
import Data.Some (Some (Some))
import Data.String (IsString (..))
import Data.Typeable
import GHC.Generics
import GHC.Natural
import qualified PlutusTx
import Shelley.Spec.Ledger.API.Genesis
import qualified Shelley.Spec.Ledger.LedgerState as LedgerState
import System.CPUTime
import Test.Cardano.Ledger.DependGraph (ModelGeneratorParamsF (..), defaultModelGeneratorParams, genModel)
import Test.Cardano.Ledger.Elaborators
import Test.Cardano.Ledger.Elaborators.Alonzo ()
import Test.Cardano.Ledger.Elaborators.Shelley ()
import Test.Cardano.Ledger.ModelChain
import Test.Cardano.Ledger.ModelChain.Address
import Test.Cardano.Ledger.ModelChain.FeatureSet
import Test.Cardano.Ledger.ModelChain.Script
import Test.Cardano.Ledger.ModelChain.Utils
import Test.Cardano.Ledger.ModelChain.Value
import Test.Shelley.Spec.Ledger.ConcreteCryptoTypes (C_Crypto)
import Test.Shelley.Spec.Ledger.Utils (testGlobals)
import Test.Tasty
import Test.Tasty.QuickCheck

modelMACoin ::
  (ValueFeature era ~ 'ExpectAnyOutput) =>
  ModelScript (ScriptFeature era) ->
  [(AssetName, Natural)] ->
  ModelValue 'ExpectAnyOutput era
modelMACoin script assets = foldMap f assets
  where
    f (asset, qty) = ModelValue $ ModelValue_Scale qty $ ModelValue_Var $ ModelValue_MA (script, asset)

modelCoin :: Integer -> ModelValue era k
modelCoin = ModelValue . ModelValue_Inject . Coin

modelReward :: ModelCredential 'Staking (ScriptFeature era) -> ModelValue k era
modelReward = ModelValue . ModelValue_Var . ModelValue_Reward

modelRewards :: [ModelCredential 'Staking (ScriptFeature era)] -> Map.Map (ModelCredential 'Staking (ScriptFeature era)) (ModelValue k era)
modelRewards = foldMap $ \maddr -> Map.singleton maddr $ modelReward maddr

scriptArity :: Tag -> Natural
scriptArity Spend = 3
scriptArity Mint = 2
scriptArity Cert = 2
scriptArity Rewrd = 2

alwaysSucceedsPlutusAddress :: ModelAddress ('TyScriptFeature x 'True)
alwaysSucceedsPlutusAddress =
  ModelAddress
    (ModelScriptHashObj $ ModelPlutusScript_AlwaysSucceeds $ scriptArity Spend)
    (ModelScriptHashObj $ ModelPlutusScript_AlwaysSucceeds $ scriptArity Cert)

infixl 7 $*

($*) :: Natural -> ModelValue era k -> ModelValue era k
x $* ModelValue y = ModelValue (ModelValue_Scale x y)

infixl 6 $+

($+) :: ModelValue era k -> ModelValue era k -> ModelValue era k
ModelValue x $+ ModelValue y = ModelValue (ModelValue_Add x y)

infixl 6 $-

($-) :: ModelValue era k -> ModelValue era k -> ModelValue era k
ModelValue x $- ModelValue y = ModelValue (ModelValue_Sub x y)

purpleModelScript :: ModelScript ('TyScriptFeature 'True x)
purpleModelScript = ModelScript_Timelock $ ModelTimelock_AllOf []

bobCoinScript :: ModelScript ('TyScriptFeature 'True x)
bobCoinScript = ModelScript_Timelock $ ModelTimelock_Signature "BobCoin"

modelPlutusScript :: Natural -> ModelScript ('TyScriptFeature x 'True)
modelPlutusScript = ModelScript_PlutusV1 . ModelPlutusScript_AlwaysSucceeds

instance IsString AssetName where
  fromString = AssetName . BS.pack

modelTestDelegations ::
  ( ElaborateEraModel era,
    Default (AdditionalGenesisConfig era),
    Show (PredicateFailure (Core.EraRule "LEDGER" era)),
    Show (Core.Value era),
    Show (Core.Tx era),
    Show (Core.Script era)
    , LedgerState.TransUTxOState Show era
  ) =>
  proxy era ->
  Bool ->
  ModelAddress AllScriptFeatures ->
  [TestTree]
modelTestDelegations proxy needsCollateral stakeAddr@(ModelAddress _ stakeCred) =
  let modelPool =
        ModelPoolParams
          "pool1"
          "pool1'"
          (Coin 0)
          (Coin 0)
          (fromJust $ boundRational $ 0 % 1)
          "rewardAcct"
          ["poolOwner"]
      modelDelegation = ModelDelegate (ModelDelegation stakeCred "pool1")
      allAtOnce =
        [ ModelBlock
            0
            [ modelTx
                { _mtxInputs = Set.fromList [0],
                  _mtxWitnessSigs = Set.fromList $ ["unstaked", "pool1", "poolOwner"] <> mapMaybe mkWitness [_modelAddress_pmt stakeAddr],
                  _mtxRedeemers = Map.fromList [x | x <- [(ModelScriptPurpose_Certifying modelDelegation, (PlutusTx.I 5, ExUnits 1 1))], needsCollateral],
                  _mtxCollateral = SupportsPlutus $ Set.fromList [x | x <- [0], needsCollateral],
                  _mtxOutputs =
                    [ (100, modelTxOut "unstaked" (modelCoin 9_800_000_000_000)),
                      (101, modelTxOut stakeAddr (modelCoin 100_000_000_000))
                    ],
                  _mtxFee = modelCoin 100_000_000_000,
                  _mtxDCert =
                    [ ModelRegisterStake stakeCred,
                      ModelRegisterPool modelPool,
                      modelDelegation
                    ]
                }
            ]
        ]
      oneAtATime =
        [ ModelBlock
            0
            [ modelTx
                { _mtxInputs = Set.fromList [0],
                  _mtxWitnessSigs = Set.fromList ["unstaked"],
                  _mtxOutputs =
                    [ (1, modelTxOut "unstaked" (modelCoin 9_875_000_000_000)),
                      (101, modelTxOut stakeAddr (modelCoin 100_000_000_000))
                    ],
                  _mtxFee = modelCoin 25_000_000_000
                }
            ],
          ModelBlock
            1
            [ modelTx
                { _mtxInputs = Set.fromList [1],
                  _mtxWitnessSigs = Set.fromList ["unstaked"],
                  _mtxOutputs =
                    [ (2, modelTxOut "unstaked" (modelCoin 9_850_000_000_000))
                    ],
                  _mtxFee = modelCoin 25_000_000_000,
                  _mtxDCert = [ModelRegisterStake stakeCred]
                }
            ],
          ModelBlock
            2
            [ modelTx
                { _mtxInputs = Set.fromList [2],
                  _mtxWitnessSigs = Set.fromList ["unstaked", "pool1", "poolOwner"],
                  _mtxOutputs =
                    [ (3, modelTxOut "unstaked" (modelCoin 9_825_000_000_000))
                    ],
                  _mtxFee = modelCoin 25_000_000_000,
                  _mtxDCert = [ModelRegisterPool modelPool]
                }
            ],
          ModelBlock
            3
            [ modelTx
                { _mtxInputs = Set.fromList [3],
                  _mtxWitnessSigs = Set.fromList $ ["unstaked"] <> mapMaybe mkWitness [_modelAddress_pmt stakeAddr],
                  _mtxRedeemers = Map.fromList [x | x <- [(ModelScriptPurpose_Certifying modelDelegation, (PlutusTx.I 5, ExUnits 1 1))], needsCollateral],
                  _mtxCollateral = SupportsPlutus $ Set.fromList [x | x <- [3], needsCollateral],
                  _mtxOutputs =
                    [ (100, modelTxOut "unstaked" (modelCoin 9_800_000_000_000))
                    ],
                  _mtxFee = modelCoin 25_000_000_000,
                  _mtxDCert =
                    [ modelDelegation
                    ]
                }
            ]
        ]
      genAct =
        [ (0, "unstaked", Coin 10_000_000_000_000)
        ]
      checkAllWithdrawnRewards nes ems =
        let rewards = observeRewards (-1, -1, -1) (nes, ems)
         in counterexample (show rewards) $ Coin 0 === fold rewards

      mkWitness = filterModelCredential (FeatureTag ValueFeatureTag_AdaOnly ScriptFeatureTag_None)

      go reg =
        testChainModelInteractionWith
          proxy
          checkAllWithdrawnRewards
          genAct
          [ ModelEpoch reg (ModelBlocksMade $ Map.fromList []),
            ModelEpoch [] (ModelBlocksMade $ Map.fromList []),
            ModelEpoch [] (ModelBlocksMade $ Map.fromList [("pool1", 100)]), -- TODO: get this from context somehow
            ModelEpoch [] (ModelBlocksMade $ Map.fromList []),
            ModelEpoch
              [ ModelBlock
                  0
                  [ modelTx
                      { _mtxInputs = Set.fromList [100],
                        _mtxWitnessSigs = Set.fromList $ ["unstaked"] <> mapMaybe mkWitness [_modelAddress_pmt stakeAddr],
                        _mtxRedeemers = Map.fromList [x | x <- [(ModelScriptPurpose_Rewarding stakeCred, (PlutusTx.I 5, ExUnits 1 1))], needsCollateral],
                        _mtxCollateral = SupportsPlutus $ Set.fromList [x | x <- [100], needsCollateral],
                        _mtxOutputs =
                          [ (103, modelTxOut "unstaked" (modelCoin 9_700_000_000_000)),
                            (104, modelTxOut "reward-less-minimum" (modelReward stakeCred $- modelCoin 100_000_000)),
                            (105, modelTxOut "minimum" (modelCoin 100_000_000))
                          ],
                        _mtxFee = modelCoin 100_000_000_000,
                        _mtxWdrl = modelRewards [stakeCred]
                      }
                  ]
              ]
              (ModelBlocksMade $ Map.fromList [])
          ]
   in [ testProperty "allAtOnce" $ go allAtOnce,
        testProperty "oneAtATime" $ go oneAtATime
      ]

genModel' ::
  forall era proxy.
  ( KnownRequiredFeatures era
  ) =>
  proxy era ->
  Globals ->
  Gen
    ( Bool,
      ( [(ModelUTxOId, ModelAddress (ScriptFeature era), Coin)],
        [ModelEpoch AllModelFeatures]
      )
    )
genModel' _ globals = do
  (a, b) <-
    genModel @era globals $
      defaultModelGeneratorParams
        { -- TODO: solve "zero withdrawal" issue, which is that some model
          -- generated withdrawals correspond to zero rewards (esp in alonzo).
          -- These numbers are chosen so that the "zero withdrawal" issue occurs
          -- rarely.
          _modelGeneratorParams_epochs = choose (8, 10),
          _modelGeneratorParams_txnsPerSlot = frequency [(1, pure 1), (0, choose (2, 15))],
          _modelGeneratorParams_numSlotsUsed = choose (2, 5)
        }
  pure (False, (a, maybe (error "fromJust") id $ traverse (filterFeatures $ FeatureTag ValueFeatureTag_AnyOutput $ ScriptFeatureTag_PlutusV1) b))

simulateChainModel ::
  (KnownScriptFeature (ScriptFeature era)) =>
  Globals ->
  [(ModelUTxOId, ModelAddress (ScriptFeature era), Coin)] ->
  [ModelEpoch era] ->
  ModelLedger era
simulateChainModel globals g e =
  flip State.execState (mkModelLedger globals modelPParams g) $
    for_ e $ \mepoch -> do
      State.modify $ execModelM (applyModelEpoch mepoch) globals

prop_simulateChainModel ::
  Testable prop =>
  Globals ->
  [(ModelUTxOId, ModelAddress sf, Coin)] ->
  [ModelEpoch AllModelFeatures] ->
  prop ->
  Property
prop_simulateChainModel globals g e = execPropertyWriter $ do
  Writer.tell $ Endo $ counterexample ("genesis:\t" <> show g)
  ((), st') :: ((), ModelLedger AllModelFeatures) <- flip
    State.runStateT
    (mkModelLedger globals modelPParams $ over (traverse . _2) liftModelAddress' g)
    $ for_ e $ \mepoch -> do
      st <- State.get
      tellProperty $ counterexample ("ledger:\t" <> show st)
      tellProperty $ counterexample ("epoch:\t" <> show mepoch)
      State.modify $ execModelM (applyModelEpoch mepoch) globals
  tellProperty $ counterexample ("final ledger state:" <> show st')

tellProperty :: Writer.MonadWriter (Endo Property) m => (Property -> Property) -> m ()
tellProperty = Writer.tell . Endo

tellProperty_ :: (Writer.MonadWriter (Endo Property) m, Testable prop) => prop -> m ()
tellProperty_ = Writer.tell . Endo . (.&&.)

execPropertyWriter :: Testable prop => Writer.Writer (Endo Property) () -> prop -> Property
execPropertyWriter x k = (flip appEndo (property k)) . Writer.execWriter $ x

execPropertyWriter_ :: Writer.Writer (Endo Property) () -> Property
execPropertyWriter_ x = (flip appEndo (property True)) . Writer.execWriter $ x

prop_null :: (Foldable f, Show (f a)) => f a -> Property
prop_null xs = counterexample (interpret res ++ show xs) res
  where
    res = null xs
    interpret True = "null "
    interpret False = "not . null $ "

checkElaboratorResult ::
  ( LedgerState.TransUTxOState Show era,
    Show (Core.Tx era)
  ) =>
  LedgerState.NewEpochState era ->
  EraElaboratorState era ->
  Property
checkElaboratorResult _nes ees = execPropertyWriter_ $ do
  let stats = (_eesStats ees)
  tellProperty $ counterexample $ (<>) "stats:" $ show stats
  tellProperty_ $ prop_null $ _eeStats_adaConservedErrors stats
  -- tellProperty $ cover 90 (_eeStats_badWdrls stats * 10 <= _eeStats_wdrls stats) "zero withdrawals < 10%"
  tellProperty $ cover 50 (_eeStats_badWdrls stats <= 0) "zero withdrawals"
  pure ()

data ModelStats f = ModelStats
  { _numberOfEpochs :: f Int,
    _numberOfTransactions :: f Int,
    _numberOfCerts :: f Int,
    _blocksMade :: f Natural,
    _numberOfDelegations :: f Int,
    _withdrawals :: f Int,
    _scriptUTxOs :: f Int,
    _scriptWdrls :: f Int
  }
  deriving (Generic)

deriving instance
  ( Show (f Natural),
    Show (f Int)
  ) =>
  Show (ModelStats f)

instance FFunctor ModelStats where ffmap = ffmapDefault

instance FZip ModelStats where fzipWith = gfzipWith

instance FRepeat ModelStats where frepeat = gfrepeat

instance FFoldable ModelStats where ffoldMap = ffoldMapDefault

instance FTraversable ModelStats where ftraverse = gftraverse

mstats :: forall era. ModelStats ((->) [ModelEpoch era])
mstats =
  ModelStats
    { _numberOfEpochs = lengthOf (traverse),
      _numberOfTransactions = lengthOf (traverse . modelTxs),
      _numberOfCerts = lengthOf (traverse . modelDCerts),
      _blocksMade = sumOf (traverse . modelEpoch_blocksMade . _ModelBlocksMade . traverse),
      _numberOfDelegations = lengthOf (traverse . modelDCerts . _ModelDelegate),
      _withdrawals = lengthOf (traverse . modelTxs . modelTx_wdrl . traverse),
      _scriptUTxOs =
        lengthOf (traverse . _2 . modelTxOut_address . modelAddress_pmt . traverseModelScriptHashObj)
          . uncurry Map.restrictKeys
          . ((_modelUTxOMap_utxos . collectModelUTxOs) &&& collectModelInputs),
      _scriptWdrls =
        lengthOf (traverse . traverseModelScriptHashObj) . (=<<) Map.keys . toListOf (traverse . modelTxs . modelTx_wdrl)
    }

shelleyFeatureTag, alonzoFeatureTag :: Some FeatureTag
shelleyFeatureTag = Some $ eraFeatureSet (Proxy :: Proxy (ShelleyEra C_Crypto))
alonzoFeatureTag = Some $ eraFeatureSet (Proxy :: Proxy (AlonzoEra C_Crypto))

mstatsCover :: ModelStats (Const (Some FeatureTag, Double, String) :*: Predicate)
mstatsCover =
  ModelStats
    { _numberOfEpochs = Const (shelleyFeatureTag, 90, "number of epochs") :*: Predicate (> 5),
      _numberOfTransactions = Const (shelleyFeatureTag, 90, "number of transactions") :*: Predicate (> 5),
      _numberOfCerts = Const (shelleyFeatureTag, 50, "number of certs") :*: Predicate (> 5),
      _blocksMade = Const (shelleyFeatureTag, 50, "blocks made") :*: Predicate (> 250),
      _numberOfDelegations = Const (shelleyFeatureTag, 10, "number of delegation") :*: Predicate (> 5),
      _withdrawals = Const (shelleyFeatureTag, 10, "withdrawals") :*: Predicate (> 5),
      _scriptUTxOs = Const (alonzoFeatureTag, 60, "script locked utxos") :*: Predicate (> 5),
      _scriptWdrls = Const (alonzoFeatureTag, 40, "script locked withdrarwals") :*: Predicate (> 5)
    }

collectModelUTxOs :: [ModelEpoch era] -> ModelUTxOMap era
collectModelUTxOs epochs =
  fold $
    [ set (at ui) (Just txo) mempty
      | tx <- toListOf (traverse . modelEpoch_blocks . traverse . modelBlock_txSeq . traverse) epochs,
        (ui, txo) <- _mtxOutputs tx
    ]

collectModelInputs :: [ModelEpoch era] -> Set.Set ModelUTxOId
collectModelInputs epochs =
  fold $
    [ _mtxInputs tx
      | tx <- toListOf (traverse . modelEpoch_blocks . traverse . modelBlock_txSeq . traverse) epochs
    ]

propModelStats ::
  forall era prop proxy.
  (Testable prop, KnownRequiredFeatures era) =>
  -- [(ModelUTxOId, ModelAddress (ScriptFeature era), Coin)] ->
  proxy era ->
  [ModelEpoch AllModelFeatures] ->
  prop ->
  Property
propModelStats proxy epochs =
  let era = reifyRequiredFeatures proxy
   in execPropertyWriter $
        ffor_ (fzipWith (:*:) mstats mstatsCover) $ \(f :*: (Const (Some era', pct, tag) :*: Predicate threshhold)) ->
          when (preceedsModelEra era' era) $
            tellProperty $ cover pct (threshhold $ f epochs) tag

examineModel ::
  [ModelEpoch era] ->
  ModelStats ((,) Bool)
examineModel epochs = fzipWith (\f (_ :*: Predicate p) -> let x = f epochs in (p x, x)) mstats mstatsCover

modelGenTest ::
  forall era proxy.
  ( ElaborateEraModel era,
    Default (AdditionalGenesisConfig era),
    Show (PredicateFailure (Core.EraRule "LEDGER" era)),
    Show (Core.Value era),
    LedgerState.TransUTxOState Show era,
    Show (Core.Tx era),
    Show (Core.Script era)
  ) =>
  proxy era ->
  Property
modelGenTest proxy =
  forAllShrink (genModel' (reifyRequiredFeatures $ Proxy @(EraFeatureSet era)) testGlobals) (shrinkModel (Proxy @(EraFeatureSet era)) testGlobals modelPParams) $ \(_ :: Bool, (a, b)) ->
    ( execPropertyWriter $ do
        tellProperty $ counterexample ("numPools: " <> show (lengthOf (traverse . modelDCerts . _ModelDelegate) b))
        tellProperty $ propModelStats (Proxy @(EraFeatureSet era)) b
    )
      (testChainModelInteractionWith proxy checkElaboratorResult a b)

testModelShrinking ::
  forall era proxy.
  ( ElaborateEraModel era,
    Default (AdditionalGenesisConfig era),
    Show (PredicateFailure (Core.EraRule "LEDGER" era)),
    Show (Core.Tx era),
    Show (Core.Script era),
    Show (Core.Value era)
    , LedgerState.TransUTxOState Show era
  ) =>
  proxy era ->
  Property
testModelShrinking proxy =
  forAll (genModel' (reifyRequiredFeatures $ Proxy @(EraFeatureSet era)) testGlobals) $ \(_ :: Bool, (a, b)) ->
    let mTxns = discardUnnecessaryTxns (Proxy @(EraFeatureSet era)) testGlobals modelPParams (a, b)
        ab'@(a', b') =
          case mTxns of
            Just (x, y) -> (x, y)
            Nothing -> (a, b)
        numBefore = (lengthOf (traverse . modelTxs)) b
        numAfter = (lengthOf (traverse . modelTxs)) b'

        mTxns' = discardUnnecessaryTxns (Proxy @(EraFeatureSet era)) testGlobals modelPParams (a', b')
        (_, j) =
          case mTxns' of
            Just (x', y') -> (x', y')
            Nothing -> (a', b')
        numAfter' = (lengthOf (traverse . modelTxs)) j
     in ( execPropertyWriter $ do
            tellProperty $ cover 55 (numAfter < numBefore) "numAfter < numBefore"
            tellProperty $ cover 55 (numAfter' == numAfter) "numAfter' == numAfter"
            tellProperty $ counterexample $ "shrunk result: ab'=" <> (show ab')
        )
          (testChainModelInteractionWith proxy checkElaboratorResult a' b')

time :: NFData t => String -> IO t -> IO t
time clue a = do
  start <- getCPUTime
  !v <- force <$> a
  end <- getCPUTime
  let diff = (fromIntegral (end - start)) / (1e12)
  putStrLn $ unwords [clue, "time:", show (diff :: Double), "sec"]
  return v

generateOneExample :: IO ()
generateOneExample = do
  let proxy = (Proxy :: Proxy (AlonzoEra C_Crypto))
      proxy' = eraFeatureSet proxy
  (_ :: Bool, (a, b)) <- time "generate" $ generate $ genModel' proxy' testGlobals
  time "examine" $ print $ examineModel b
  _mresult <- time "modelApp" $ pure $ simulateChainModel testGlobals a b
  result <- time "elaborate" $ pure $ fst &&& (_eesStats . snd . snd) $ chainModelInteractionWith proxy a b
  print result

-- | Shrink the epochs down to txns and each element will have its own prefix of txns, including all txns that came before.
-- This function also includes a prefix where there is a block with no transactions.
shrinkModelSimple ::
  (a, [ModelEpoch AllModelFeatures]) ->
  [(a, [ModelEpoch AllModelFeatures])]
shrinkModelSimple (genesis, epochs) = (,) genesis <$> (List.init $ shrinkModelEpochs epochs)
  where
    getBlockPrefixes ::
      ModelBlock era ->
      [ModelBlock era]
    getBlockPrefixes (ModelBlock slotNo txns) = (ModelBlock slotNo) <$> (List.inits txns)

    getEpochPrefixes ::
      ModelEpoch AllModelFeatures ->
      [ModelEpoch AllModelFeatures]
    getEpochPrefixes (ModelEpoch blocks blocksMade) =
      let blockPrefixes = snd $ foldl (appendPrefixes getBlockPrefixes) ([], []) blocks
       in (flip ModelEpoch blocksMade) <$> blockPrefixes

    -- This function produces a tuple
    -- The first value is to keep track of any previous blocks/epochs
    -- The second value is the previous blocks/epochs plus the prefixes of each block/epoch
    appendPrefixes ::
      (b -> [b]) ->
      ([b], [[b]]) ->
      b ->
      ([b], [[b]])
    appendPrefixes getPrefixsFn (accumulatedXs, prefixList) x =
      let addPrevXsFn = (<>) accumulatedXs
          newPrefixes = addPrevXsFn <$> (pure <$> (getPrefixsFn x))
       in (accumulatedXs <> [x], prefixList <> newPrefixes)

    shrinkModelEpochs ::
      [ModelEpoch AllModelFeatures] ->
      [[ModelEpoch AllModelFeatures]]
    shrinkModelEpochs es = snd $ foldl (appendPrefixes getEpochPrefixes) ([], []) es

data TxFieldChecks era = TxFieldChecks
  { txFieldChecks_UTxOIds :: Set.Set ModelUTxOId,
    txFieldChecks_Delegators :: Set.Set (ModelCredential 'Staking (ScriptFeature era)),
    txFieldChecks_Delegatees :: Set.Set ModelPoolId,
    txFieldChecks_ModelTxNo :: Set.Set ModelTxNo
  }

data TrackDeps era = TrackDeps
  { trackDeps_genesis :: [(ModelUTxOId, ModelAddress (ScriptFeature era), Coin)],
    trackDeps_txFieldChecks :: TxFieldChecks era,
    trackDeps_currentTxNo :: ModelTxNo,
    trackDeps_prevEpochs :: [ModelEpoch era]
  }

discardUnnecessaryTxns ::
  forall era.
  Proxy era ->
  Globals ->
  Alonzo.PParams () ->
  ([(ModelUTxOId, ModelAddress (ScriptFeature era), Coin)], [ModelEpoch AllModelFeatures]) ->
  Maybe ([(ModelUTxOId, ModelAddress (ScriptFeature era), Coin)], [ModelEpoch AllModelFeatures])
discardUnnecessaryTxns _ _ _ (_, []) = Nothing
discardUnnecessaryTxns _ globals pp (genesis, epochs) =
  let lastEpochsTxns = toListOf modelTxs $ last epochs
      liftedGenesis = fmap (\(x, y, z) -> (x, liftModelAddress' y, z)) genesis
      (initialTxFieldChecks, initialTxn) = getInitialInfo liftedGenesis (init' epochs) lastEpochsTxns
      totalModelTxs = toInteger $ lengthOf (traverse . modelTxs) epochs

      (_, shrunkenEpochs) =
        foldr
          checkEpoch
          (TrackDeps liftedGenesis initialTxFieldChecks (ModelTxNo totalModelTxs) $ init' epochs, [])
          epochs
      lastOfShrunkenEpochs = last shrunkenEpochs
      lastEpoch = lastOfShrunkenEpochs {_modelEpoch_blocks = addInitialTxn (_modelEpoch_blocks lastOfShrunkenEpochs) initialTxn}

      newEpochs = (init shrunkenEpochs) <> [lastEpoch]
   in if (epochs == newEpochs)
        then Nothing
        else Just (genesis, newEpochs)
  where
    init' [] = []
    init' es' = init es'

    emptyTxFieldChecks :: forall era'. TxFieldChecks era'
    emptyTxFieldChecks = TxFieldChecks Set.empty Set.empty Set.empty Set.empty

    -- This function is to get the counter-example's TxFieldChecks and the offending transaction
    getInitialInfo ::
      forall era'.
      KnownScriptFeature (ScriptFeature era') =>
      [(ModelUTxOId, ModelAddress (ScriptFeature era'), Coin)] ->
      [ModelEpoch era'] ->
      [ModelTx era'] ->
      (TxFieldChecks era', [ModelTx era'])
    getInitialInfo _ _ [] = (emptyTxFieldChecks, [])
    getInitialInfo g es ts =
      let lastTx = last ts
          inputs = lastTx ^. modelTx_inputs
          delegates = toListOf (modelTx_dCert . traverse . _ModelDelegate) lastTx
          txDelegators = Set.fromList $ _mdDelegator <$> delegates
          txDelegatees = Set.fromList $ _mdDelegatee <$> delegates

          -- here we are checking whether the delegations deps are within the same tx
          -- already keeping the initial tx
          (_, (TxFieldChecks _ delegatorsLeft delegateesLeft _)) =
            checkTxDelegationDeps
              (TxFieldChecks [] txDelegators txDelegatees [])
              (lastTx ^. modelTx_dCert)

          txWdrls = lastTx ^. modelTx_wdrl
          updatedFieldChecks =
            trackWdrlDeps txWdrls (TxFieldChecks inputs delegatorsLeft delegateesLeft []) $
              TrackDeps g emptyTxFieldChecks (-1) es
       in (updatedFieldChecks, [lastTx])

    -- This function adds the orignal counter-example transaction into the shrunken Epochs
    addInitialTxn [] _ = []
    addInitialTxn bs t =
      let lastBlock = last bs
          updatedLastBlock = lastBlock {_modelBlock_txSeq = (_modelBlock_txSeq lastBlock) <> t}
       in (init bs) <> [updatedLastBlock]

    checkTxNo ::
      forall era'.
      ModelTxNo ->
      TxFieldChecks era' ->
      (Bool, TxFieldChecks era')
    checkTxNo currentTxNo (TxFieldChecks utxos dors dees txNos) =
      let bMatchingTxNo = elem currentTxNo txNos
          newTxNos = Set.filter ((/=) currentTxNo) txNos
       in (bMatchingTxNo, TxFieldChecks utxos dors dees newTxNos)

    -- This function will return a bool to indicate whether to keep the tx and filter out any matching fields
    checkTxDelegationDeps ::
      forall era'.
      TxFieldChecks era' ->
      [ModelDCert era'] ->
      (Bool, TxFieldChecks era')
    checkTxDelegationDeps (TxFieldChecks uTxOIds prevDelegators prevDelegatees modelTxNos) dCerts =
      let delegateeIds = (fmap _mppId . toListOf (traverse . _ModelRegisterPool)) dCerts
          delegators = toListOf (traverse . _ModelRegisterStake) dCerts

          bMatchingDelegateeIds = not . null $ Set.intersection (Set.fromList delegateeIds) prevDelegatees
          bMatchingDelegators = not . null $ Set.intersection (Set.fromList delegators) prevDelegators
          updatedDelegateeIds = Set.difference prevDelegatees (Set.fromList delegateeIds)
          updatedDelegators = Set.difference prevDelegators (Set.fromList delegators)
       in ( bMatchingDelegateeIds || bMatchingDelegators,
            TxFieldChecks uTxOIds updatedDelegators updatedDelegateeIds modelTxNos
          )

    getTxNos :: ModelRewardProvenance -> Set.Set ModelTxNo
    getTxNos (ModelRewardProvenance_Delegate (ModelRewardProvenanceDelegate s p d)) = Set.fromList [s, p, d]
    getTxNos (ModelRewardProvenance_Pool (ModelRewardProvenancePool p)) = Set.singleton p

    trackWdrlDeps ::
      forall era'.
      KnownScriptFeature (ScriptFeature era') =>
      Map.Map (ModelCredential 'Staking (ScriptFeature era')) (ModelValue 'ExpectAdaOnly era') ->
      TxFieldChecks era' ->
      TrackDeps era' ->
      TxFieldChecks era'
    trackWdrlDeps wdrls txFieldChecks@(TxFieldChecks utxos delegators delegatees txNos) (TrackDeps g _ _ prevEpochs)
      | wdrls == Map.empty = txFieldChecks
      | otherwise =
        let mLedger = execModelM
              (for_ prevEpochs $ \me -> applyModelEpoch me)
              globals
              (mkModelLedger globals pp g)
            wdrlAddrSet = Map.keysSet wdrls
            mLedgerRewards = unGrpMap $ mLedger ^. modelLedger_rewardsProv
            addrsRewards = concat $ Map.elems <$> (Map.elems $ Map.restrictKeys mLedgerRewards wdrlAddrSet)

            rewardModelUTxOIds = foldr Set.union Set.empty $ fst <$> addrsRewards
            rewardTxNos = foldr Set.union Set.empty $ fmap getTxNos $ snd <$> addrsRewards
         in TxFieldChecks (utxos <> rewardModelUTxOIds) delegators delegatees $ txNos <> rewardTxNos

    -- This function checks whether to keep a tx. Appends it to list of txs to keep and tracks it's dependencies
    checkTx ::
      forall era'.
      KnownScriptFeature (ScriptFeature era') =>
      ModelTx era' ->
      (TrackDeps era', [ModelTx era']) ->
      (TrackDeps era', [ModelTx era'])
    checkTx txToCheck ogTuple@(TrackDeps g txFieldChecks currentTxNo prevEpochs, txsToKeep) =
      -- Check if current tx outputs any tx of Interests
      let txOutputsUTxOIds = Set.fromList $ fst <$> txToCheck ^. modelTx_outputs
          trackedUTxOIds = txFieldChecks_UTxOIds txFieldChecks
          bMatchingUTxOIds = not . null $ Set.intersection txOutputsUTxOIds trackedUTxOIds

          txDCerts = toList $ txToCheck ^. modelTx_dCert
          (keepTx', updatedDelegFieldChecks) = checkTxDelegationDeps txFieldChecks txDCerts

          (keepTx, updatedDelegWdrlFieldChecks') =
            checkTxNo currentTxNo updatedDelegFieldChecks
          newTxNo = currentTxNo - 1
       in case (bMatchingUTxOIds || keepTx || keepTx') of
            False -> ((fst ogTuple) {trackDeps_currentTxNo = newTxNo}, txsToKeep)
            _ ->
              -- tx is tx of interest
              let updatedTrackedUTxOIds = Set.difference trackedUTxOIds txOutputsUTxOIds
                  txInputs = txToCheck ^. modelTx_inputs
                  -- track inputs of tx
                  updatedUTxOIds = txInputs <> updatedTrackedUTxOIds

                  (TxFieldChecks wdrlUTxOIds prevDelegators prevDelegatees txNos) =
                    trackWdrlDeps (txToCheck ^. modelTx_wdrl) updatedDelegWdrlFieldChecks' $ fst ogTuple

                  txDelegations = toListOf (traverse . _ModelDelegate) txDCerts
                  txDelegators = Set.fromList $ _mdDelegator <$> txDelegations
                  txDelegatees = Set.fromList $ _mdDelegatee <$> txDelegations
                  -- We want to check whether Delegation Deps are within the same tx's _mtxDCerts
                  (alreadyFound, (TxFieldChecks _ delegatorsLeft delegateesLeft _)) =
                    checkTxDelegationDeps
                      (TxFieldChecks [] txDelegators txDelegatees [])
                      txDCerts
                  -- Only add if not already found within same txn
                  (updatedDelegators, updatedDelegatees) = case alreadyFound of
                    True -> (prevDelegators <> delegatorsLeft, prevDelegatees <> delegateesLeft)
                    False -> (prevDelegators <> txDelegators, prevDelegatees <> txDelegatees)

                  newTxFieldChecks =
                    TxFieldChecks (updatedUTxOIds <> wdrlUTxOIds) updatedDelegators updatedDelegatees txNos
               in (TrackDeps g newTxFieldChecks newTxNo prevEpochs, txToCheck : txsToKeep)

    checkBlock ::
      forall era'.
      KnownScriptFeature (ScriptFeature era') =>
      ModelBlock era' ->
      (TrackDeps era', [ModelBlock era']) ->
      (TrackDeps era', [ModelBlock era'])
    checkBlock (ModelBlock slotNo txs) (trackDeps, trackedBlocks) =
      let (newTrackDeps, newTxs) = foldr checkTx (trackDeps, []) txs
       in (newTrackDeps, (ModelBlock slotNo newTxs) : trackedBlocks)

    checkEpoch ::
      forall era'.
      KnownScriptFeature (ScriptFeature era') =>
      ModelEpoch era' ->
      (TrackDeps era', [ModelEpoch era']) ->
      (TrackDeps era', [ModelEpoch era'])
    checkEpoch (ModelEpoch blocks blocksMade) (trackDeps, trackedEpochs) =
      let (TrackDeps g newUTxOIds newTxNo es, newBlocks) = foldr checkBlock (trackDeps, []) blocks
       in (TrackDeps g newUTxOIds newTxNo $ init' es, (ModelEpoch newBlocks blocksMade) : trackedEpochs)

shrinkModel ::
  Proxy era ->
  Globals ->
  Alonzo.PParams () ->
  ( Bool,
    ( [(ModelUTxOId, ModelAddress (ScriptFeature era), Coin)],
      [ModelEpoch AllModelFeatures]
    )
  ) ->
  [ ( Bool,
      ( [(ModelUTxOId, ModelAddress (ScriptFeature era), Coin)],
        [ModelEpoch AllModelFeatures]
      )
    )
  ]
shrinkModel p globals pp = shrinkPhases shrinkModelSimple (\x -> maybe [] (\y -> [y]) $ discardUnnecessaryTxns p globals pp x)
  where
    shrinkPhases f _ (False, x) = ((,) True) <$> (f x)
    shrinkPhases _ g (True, x) = ((,) True) <$> (g x)

-- | some hand-written model based unit tests
modelUnitTests ::
  forall era proxy.
  ( ElaborateEraModel era,
    Default (AdditionalGenesisConfig era),
    Eq (PredicateFailure (Core.EraRule "LEDGER" era)),
    Show (PredicateFailure (Core.EraRule "LEDGER" era)),
    Show (Core.Value era),
    LedgerState.TransUTxOState Show era,
    Show (Core.Tx era),
    Show (Core.Script era)
  ) =>
  proxy era ->
  TestTree
modelUnitTests proxy =
  testGroup
    (show $ typeRep proxy)
    [ testProperty "gen" $ checkCoverage $ modelGenTest proxy,
      testProperty "gen Always shrink" $ checkCoverage $ testModelShrinking proxy,
      testProperty "noop" $ testChainModelInteraction proxy [] [],
      testProperty "noop-2" $
        testChainModelInteraction
          proxy
          ( [ (0, "alice", Coin 1_000_000),
              (1, "bob", Coin 1_000_000)
            ]
          )
          [ModelEpoch [] mempty],
      testGroup "deleg-keyHash" $ modelTestDelegations proxy False "keyHashStake",
      testGroup "deleg-plutus" $ modelTestDelegations proxy True alwaysSucceedsPlutusAddress,
      testProperty "xfer" $
        testChainModelInteraction
          proxy
          ( [ (0, "alice", Coin 1_000_000_000)
            ]
          )
          [ ModelEpoch
              [ ModelBlock
                  1
                  [ modelTx
                      { _mtxInputs = Set.fromList [0],
                        _mtxOutputs =
                          [ (1, modelTxOut "bob" (modelCoin 100_000_000)),
                            (2, modelTxOut "alice" (modelCoin 1_000_000_000 $- (modelCoin 100_000_000 $+ modelCoin 1_000_000)))
                          ],
                        _mtxFee = modelCoin 1_000_000,
                        _mtxWitnessSigs = Set.fromList ["alice"]
                      }
                  ]
              ]
              mempty
          ],
      testProperty "unbalanced" $
        testChainModelInteractionRejection
          proxy
          (ModelValueNotConservedUTxO (modelCoin 1_000_000_000) (modelCoin 101_000_000))
          ( [ (0, "alice", Coin 1_000_000_000)
            ]
          )
          [ ModelEpoch
              [ ModelBlock
                  1
                  [ modelTx
                      { _mtxInputs = (Set.fromList [0]),
                        _mtxWitnessSigs = Set.fromList ["alice"],
                        _mtxOutputs = [(1, modelTxOut "bob" $ modelCoin 100_000_000)],
                        _mtxFee = modelCoin 1_000_000
                      }
                  ]
              ]
              mempty
          ],
      testProperty "xfer-2" $
        testChainModelInteraction
          proxy
          ( [ (0, "alice", Coin 1_000_000_000)
            ]
          )
          [ ModelEpoch
              [ ModelBlock
                  1
                  [ modelTx
                      { _mtxInputs = Set.fromList [0],
                        _mtxWitnessSigs = Set.fromList ["alice"],
                        _mtxOutputs =
                          [ (1, modelTxOut "bob" (modelCoin 100_000_000)),
                            (2, modelTxOut "alice" (modelCoin 1_000_000_000 $- (modelCoin 100_000_000 $+ modelCoin 1_000_000)))
                          ],
                        _mtxFee = modelCoin 1_000_000
                      }
                  ],
                ModelBlock
                  2
                  [ modelTx
                      { _mtxInputs = Set.fromList [2],
                        _mtxWitnessSigs = Set.fromList ["alice"],
                        _mtxOutputs =
                          [ (3, modelTxOut "bob" (modelCoin 100_000_000)),
                            (4, modelTxOut "alice" (modelCoin 1_000_000_000 $- 2 $* (modelCoin 100_000_000 $+ modelCoin 1_000_000)))
                          ],
                        _mtxFee = modelCoin 1_000_000
                      }
                  ]
              ]
              mempty
          ],
      testProperty "mint" $
        ( testChainModelInteraction
            proxy
            ( [ (0, "alice", Coin 1_000_000_000)
              ]
            )
        )
          [ ModelEpoch
              [ ModelBlock
                  1
                  [ modelTx
                      { _mtxInputs = Set.fromList [0],
                        _mtxWitnessSigs = Set.fromList ["alice"],
                        _mtxOutputs =
                          [ ( 1,
                              modelTxOut
                                "alice"
                                ( modelCoin 1_000_000_000 $- (modelCoin 1_000_000)
                                    $+ modelMACoin purpleModelScript [("purp", 1234)]
                                )
                            )
                          ],
                        _mtxFee = modelCoin 1_000_000,
                        _mtxMint = SupportsMint (modelMACoin purpleModelScript [("purp", 1234)])
                      }
                  ]
              ]
              mempty
          ],
      testProperty "mint-2" $
        ( testChainModelInteraction
            proxy
            ( [ (0, "alice", Coin 1_000_000_000)
              ]
            )
        )
          [ ModelEpoch
              [ ModelBlock
                  1
                  [ modelTx
                      { _mtxInputs = Set.fromList [0],
                        _mtxWitnessSigs = Set.fromList ["alice", "BobCoin"],
                        _mtxOutputs =
                          [ ( 1,
                              modelTxOut
                                "alice"
                                ( modelCoin 1_000_000_000 $- (modelCoin 1_000_000)
                                    $+ modelMACoin bobCoinScript [("BOB", 1234)]
                                )
                            )
                          ],
                        _mtxFee = modelCoin 1_000_000,
                        _mtxMint = SupportsMint (modelMACoin bobCoinScript [("BOB", 1234)])
                      }
                  ]
              ]
              mempty
          ],
      testProperty "mint-3" $
        ( testChainModelInteraction
            proxy
            ( [ (0, "alice", Coin 1_000_000_000)
              ]
            )
        )
          [ ModelEpoch
              [ ModelBlock
                  1
                  [ modelTx
                      { _mtxInputs = Set.fromList [0],
                        _mtxWitnessSigs = Set.fromList ["alice"],
                        _mtxOutputs =
                          [ ( 1,
                              modelTxOut
                                "alice"
                                ( modelCoin 1_000_000_000 $- (modelCoin 1_000_000)
                                    $+ modelMACoin purpleModelScript [("BOB", 1234)]
                                )
                            )
                          ],
                        _mtxFee = modelCoin 1_000_000,
                        _mtxMint = SupportsMint (modelMACoin purpleModelScript [("BOB", 1234)])
                      },
                    modelTx
                      { _mtxInputs = Set.fromList [1],
                        _mtxWitnessSigs = Set.fromList ["alice"],
                        _mtxOutputs =
                          [ ( 2,
                              modelTxOut
                                "alice"
                                ( modelCoin 1_000_000_000 $- (3 $* modelCoin 1_000_000)
                                    $+ modelMACoin purpleModelScript [("BOB", 1134)]
                                )
                            ),
                            ( 3,
                              modelTxOut
                                "carol"
                                ( modelCoin 1_000_000
                                    $+ modelMACoin purpleModelScript [("BOB", 100)]
                                )
                            )
                          ],
                        _mtxFee = modelCoin 1_000_000
                      }
                  ]
              ]
              mempty
          ],
      testProperty "mint-4" $
        ( testChainModelInteraction
            proxy
            ( [ (0, "alice", Coin 1_000_000_000)
              ]
            )
        )
          [ ModelEpoch
              [ ModelBlock
                  1
                  [ modelTx
                      { _mtxInputs = Set.fromList [0],
                        _mtxWitnessSigs = Set.fromList ["alice", "BobCoin"],
                        _mtxOutputs =
                          [ ( 1,
                              modelTxOut
                                "alice"
                                ( modelCoin 1_000_000_000 $- (modelCoin 1_000_000)
                                    $+ modelMACoin bobCoinScript [("BOB", 1234)]
                                )
                            )
                          ],
                        _mtxFee = modelCoin 1_000_000,
                        _mtxMint = SupportsMint (modelMACoin bobCoinScript [("BOB", 1234)])
                      },
                    modelTx
                      { _mtxInputs = Set.fromList [1],
                        _mtxWitnessSigs = Set.fromList ["alice"],
                        _mtxOutputs =
                          [ ( 2,
                              modelTxOut
                                "alice"
                                ( modelCoin 1_000_000_000 $- (3 $* modelCoin 1_000_000)
                                    $+ modelMACoin bobCoinScript [("BOB", 1134)]
                                )
                            ),
                            ( 3,
                              modelTxOut
                                "carol"
                                ( modelCoin 1_000_000
                                    $+ modelMACoin bobCoinScript [("BOB", 100)]
                                )
                            )
                          ],
                        _mtxFee = modelCoin 1_000_000
                      }
                  ]
              ]
              mempty
          ],
      testProperty "mint-plutus" $
        testChainModelInteraction
          proxy
          ( [ (0, "alice", Coin 1_000_000_000)
            ]
          )
          [ ModelEpoch
              [ ModelBlock
                  1
                  [ modelTx
                      { _mtxInputs = Set.fromList [0],
                        _mtxWitnessSigs = Set.fromList ["alice"],
                        _mtxRedeemers = Map.singleton (ModelScriptPurpose_Minting $ modelPlutusScript 3) (PlutusTx.I 7, ExUnits 1 1),
                        _mtxCollateral = SupportsPlutus (Set.fromList [0]),
                        _mtxOutputs =
                          [ ( 1,
                              modelTxOut
                                "alice"
                                ( modelCoin 1_000_000_000 $- (modelCoin 1_000_000)
                                    $+ modelMACoin (modelPlutusScript 3) [("purp", 1234)]
                                )
                            )
                          ],
                        _mtxFee = modelCoin 1_000_000,
                        _mtxMint = SupportsMint (modelMACoin (modelPlutusScript 3) [("purp", 1234)])
                      }
                  ]
              ]
              mempty
          ],
      testProperty "tx-plutus" $
        testChainModelInteraction
          proxy
          ( [ (0, "alice", Coin 1_000_000_000)
            ]
          )
          [ ModelEpoch
              [ ModelBlock
                  1
                  [ modelTx
                      { _mtxInputs = Set.fromList [0],
                        _mtxWitnessSigs = Set.fromList ["alice"],
                        _mtxOutputs =
                          [ (1, modelTxOut "bob" (modelCoin 100_000_000)),
                            ( 2,
                              (modelTxOut alwaysSucceedsPlutusAddress (modelCoin 1_000_000_000 $- (modelCoin 100_000_000 $+ modelCoin 1_000_000)))
                                { _mtxo_data = SupportsPlutus $ Just $ PlutusTx.I 7
                                }
                            )
                          ],
                        _mtxFee = modelCoin 1_000_000
                      }
                  ],
                ModelBlock
                  2
                  [ modelTx
                      { _mtxInputs = Set.fromList [2],
                        _mtxWitnessSigs = Set.fromList ["bob"],
                        _mtxRedeemers = Map.singleton (ModelScriptPurpose_Spending 2) (PlutusTx.I 7, ExUnits 1 1),
                        _mtxCollateral = SupportsPlutus (Set.fromList [1]),
                        _mtxOutputs =
                          [ (3, modelTxOut "bob" (modelCoin 100_000_000)),
                            (4, modelTxOut "alice" (modelCoin 1_000_000_000 $- 2 $* (modelCoin 100_000_000 $+ modelCoin 1_000_000)))
                          ],
                        _mtxFee = modelCoin 1_000_000
                      }
                  ]
              ]
              mempty
          ]
    ]

shrinkSimpleTestData :: [ModelEpoch AllModelFeatures]
shrinkSimpleTestData =
  [ ModelEpoch
      [ ModelBlock 1 [modelTx {_mtxInputs = [1]}, modelTx {_mtxInputs = [2]}, modelTx {_mtxInputs = [3]}],
        ModelBlock 2 [modelTx {_mtxInputs = [4]}, modelTx {_mtxInputs = [5]}, modelTx {_mtxInputs = [6]}],
        ModelBlock 3 [modelTx {_mtxInputs = [7]}, modelTx {_mtxInputs = [8]}, modelTx {_mtxInputs = [9]}]
      ]
      mempty,
    ModelEpoch
      [ ModelBlock 4 [modelTx {_mtxInputs = [10]}, modelTx {_mtxInputs = [11]}, modelTx {_mtxInputs = [12]}],
        ModelBlock 5 [modelTx {_mtxInputs = [13]}, modelTx {_mtxInputs = [14]}, modelTx {_mtxInputs = [15]}],
        ModelBlock 6 [modelTx {_mtxInputs = [16]}, modelTx {_mtxInputs = [17]}, modelTx {_mtxInputs = [18]}]
      ]
      mempty,
    ModelEpoch
      [ ModelBlock 7 [modelTx {_mtxInputs = [19]}, modelTx {_mtxInputs = [20]}, modelTx {_mtxInputs = [21]}],
        ModelBlock 8 [modelTx {_mtxInputs = [22]}, modelTx {_mtxInputs = [23]}, modelTx {_mtxInputs = [24]}],
        ModelBlock 9 [modelTx {_mtxInputs = [25]}, modelTx {_mtxInputs = [26]}, modelTx {_mtxInputs = [27]}]
      ]
      mempty
  ]



shrinkDiscardTestData :: [ModelEpoch AllModelFeatures]
shrinkDiscardTestData =
  let defaultTxOut = modelTxOut "bob" (modelCoin 0)
      mkTestPool poolId racct owners = ModelPoolParams
        { _mppId = ModelPoolId $ ModelKeyHashObj poolId,
          _mppVrm = ModelKeyHashObj poolId,
          _mppPledge = Coin 0,
          _mppCost = Coin 0,
          _mppMargin =(fromJust $ boundRational $ 0 % 1),
          _mppRAcnt = racct,
          _mppOwners = owners
        }
      testPool = mkTestPool "pool1" "rewardAcct" ["poolOwner"]
      testPool2 = mkTestPool "pool2" "rewardAcct2" ["poolOwner2"]
      testPool3 = mkTestPool "pool3" "rewardAcct3" ["poolOwner3"]
   in [ ModelEpoch
          [ ModelBlock
              1
              [ modelTx {_mtxInputs = [1], _mtxOutputs = [(6, defaultTxOut)]},
                modelTx {_mtxInputs = [2], _mtxOutputs = [(5, defaultTxOut)]},
                modelTx {_mtxInputs = [3], _mtxOutputs = [(4, defaultTxOut)]}
              ],
            ModelBlock
              2
              [ modelTx {_mtxInputs = [4], _mtxOutputs = [(8, defaultTxOut), (9, defaultTxOut)]},
                modelTx {_mtxInputs = [5], _mtxDCert = [ModelRegisterStake "someAddress3"]},
                modelTx {_mtxInputs = [6], _mtxOutputs = [(7, defaultTxOut)]}
              ],
            ModelBlock
              3
              [ modelTx {_mtxInputs = [7], _mtxOutputs = [(11, defaultTxOut), (12, defaultTxOut)]},
                modelTx {_mtxInputs = [8], _mtxDCert = [ModelRegisterPool testPool3]},
                modelTx {_mtxInputs = [9], _mtxOutputs = [(10, defaultTxOut)]}
              ]
          ]
          mempty,
        ModelEpoch
          [ ModelBlock
              4
              [ modelTx {_mtxInputs = [10], _mtxOutputs = [(14, defaultTxOut), (15, defaultTxOut)]},
                modelTx {_mtxInputs = [11]},
                modelTx {_mtxInputs = [12], _mtxOutputs = [(13, defaultTxOut)], _mtxDCert = [ModelDelegate (ModelDelegation "someAddress3" "pool3")]}
              ],
            ModelBlock
              5
              [ modelTx {_mtxInputs = [13], _mtxOutputs = [(17, defaultTxOut), (18, defaultTxOut)]},
                modelTx {_mtxInputs = [14], _mtxDCert = [ModelRegisterStake "someAddress2"]},
                modelTx {_mtxInputs = [15], _mtxOutputs = [(16, defaultTxOut)]}
              ],
            ModelBlock
              6
              [ modelTx {_mtxInputs = [16], _mtxOutputs = [(20, defaultTxOut), (21, defaultTxOut)]},
                modelTx {_mtxInputs = [17], _mtxDCert = [ModelRegisterPool testPool2]},
                modelTx {_mtxInputs = [18], _mtxOutputs = [(19, defaultTxOut)]}
              ]
          ]
          mempty,
        ModelEpoch
          [ ModelBlock
              7
              [ modelTx {_mtxInputs = [19], _mtxOutputs = [(23, defaultTxOut), (24, defaultTxOut)]},
                modelTx {_mtxInputs = [20], _mtxDCert = [ModelRegisterStake "someAddress"]},
                modelTx {_mtxInputs = [21], _mtxOutputs = [(22, defaultTxOut)]}
              ],
            ModelBlock
              8
              [ modelTx {_mtxInputs = [22], _mtxOutputs = [(26, defaultTxOut), (27, defaultTxOut)]},
                modelTx {_mtxInputs = [23], _mtxDCert = [ModelRegisterPool testPool]},
                modelTx {_mtxInputs = [24], _mtxOutputs = [(25, defaultTxOut)]}
              ],
            ModelBlock
              9
              [ modelTx {_mtxInputs = [25]},
                modelTx {_mtxInputs = [26], _mtxDCert = [ModelDelegate (ModelDelegation "someAddress2" "pool2")]},
                modelTx {_mtxInputs = [27], _mtxDCert = [ModelDelegate (ModelDelegation "someAddress" "pool1")]}
              ]
          ]
          mempty
      ]

testShrinkModelSimple :: [((), [ModelEpoch AllModelFeatures])]
testShrinkModelSimple = shrinkModelSimple ((), shrinkSimpleTestData)

modelShrinkingUnitTests :: TestTree
modelShrinkingUnitTests =
  testGroup
    "model-shrinking-unit-tests"
    [ testProperty "test simple shrink" $
        let x = shrinkModelSimple ((), shrinkSimpleTestData)
            y =
              ( (),
                [ ModelEpoch
                    [ ModelBlock 1 [modelTx {_mtxInputs = [1]}, modelTx {_mtxInputs = [2]}, modelTx {_mtxInputs = [3]}],
                      ModelBlock 2 [modelTx {_mtxInputs = [4]}, modelTx {_mtxInputs = [5]}, modelTx {_mtxInputs = [6]}],
                      ModelBlock 3 [modelTx {_mtxInputs = [7]}, modelTx {_mtxInputs = [8]}, modelTx {_mtxInputs = [9]}]
                    ]
                    mempty,
                  ModelEpoch
                    [ ModelBlock 4 [modelTx {_mtxInputs = [10]}, modelTx {_mtxInputs = [11]}, modelTx {_mtxInputs = [12]}],
                      ModelBlock 5 [modelTx {_mtxInputs = [13]}, modelTx {_mtxInputs = [14]}, modelTx {_mtxInputs = [15]}],
                      ModelBlock 6 [modelTx {_mtxInputs = [16]}, modelTx {_mtxInputs = [17]}, modelTx {_mtxInputs = [18]}]
                    ]
                    mempty,
                  ModelEpoch
                    [ ModelBlock 7 [modelTx {_mtxInputs = [19]}, modelTx {_mtxInputs = [20]}, modelTx {_mtxInputs = [21]}],
                      ModelBlock 8 [modelTx {_mtxInputs = [22]}, modelTx {_mtxInputs = [23]}, modelTx {_mtxInputs = [24]}],
                      ModelBlock 9 [modelTx {_mtxInputs = [25]}, modelTx {_mtxInputs = [26]}]
                    ]
                    mempty
                ]
              )
         in head x === ((), [ModelEpoch [ModelBlock 1 []] mempty])
              .&&. List.last x === y
    ]

modelUnitTests_ :: TestTree
modelUnitTests_ =
  testGroup
    "model-unit-tests"
    [ modelUnitTests (Proxy :: Proxy (ShelleyEra C_Crypto)),
      modelUnitTests (Proxy :: Proxy (AlonzoEra C_Crypto)),
      modelShrinkingUnitTests
    ]

defaultTestMain :: IO ()
defaultTestMain = defaultMain modelUnitTests_
