{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NumDecimals #-}
{-# LANGUAGE NumericUnderscores #-}
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
import Cardano.Ledger.BaseTypes (Globals (..), boundRational)
import Cardano.Ledger.Coin
import qualified Cardano.Ledger.Core as Core
import Cardano.Ledger.Mary.Value (AssetName (..))
import Cardano.Ledger.Shelley (ShelleyEra)
import Control.DeepSeq
import Control.Lens
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
import Data.Maybe (fromJust)
import Data.Monoid (Endo (..))
import Data.Ratio ((%))
import qualified Data.Set as Set
import Data.String (IsString (..))
import Data.Typeable
import GHC.Generics
import GHC.Natural
import qualified PlutusTx
import Shelley.Spec.Ledger.API.Genesis
import qualified Shelley.Spec.Ledger.LedgerState as LedgerState
import System.CPUTime
import Test.Cardano.Ledger.DependGraph (GenActionContextF (..), defaultGenActionContext, genModel)
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

modelReward :: ModelAddress (ScriptFeature era) -> ModelValue k era
modelReward = ModelValue . ModelValue_Var . ModelValue_Reward

modelRewards :: [ModelAddress (ScriptFeature era)] -> Map.Map (ModelAddress (ScriptFeature era)) (ModelValue k era)
modelRewards = foldMap $ \maddr -> Map.singleton maddr $ modelReward maddr

infixl 6 $+

infixl 6 $-

infixl 7 $*

($*) :: Natural -> ModelValue era k -> ModelValue era k
x $* ModelValue y = ModelValue (ModelValue_Scale x y)

($+) :: ModelValue era k -> ModelValue era k -> ModelValue era k
ModelValue x $+ ModelValue y = ModelValue (ModelValue_Add x y)

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
    -- Eq (PredicateFailure (Core.EraRule "LEDGER" era)),
    Show (PredicateFailure (Core.EraRule "LEDGER" era)),
    Show (Core.Value era)
  ) =>
  proxy era ->
  Bool ->
  ModelAddress AllScriptFeatures ->
  [TestTree]
modelTestDelegations proxy needsCollateral stakeAddr =
  let modelPool = ModelPoolParams "pool1" (Coin 0) (Coin 0) (fromJust $ boundRational $ 0 % 1) "rewardAcct" ["poolOwner"]
      allAtOnce =
        [ ModelBlock
            0
            [ modelTx
                { _mtxInputs = Set.fromList [0],
                  _mtxCollateral = SupportsPlutus $ Set.fromList [x | x <- [0], needsCollateral],
                  _mtxOutputs =
                    [ (100, modelTxOut "unstaked" (modelCoin 9_800_000_000_000)),
                      (101, modelTxOut stakeAddr (modelCoin 100_000_000_000))
                    ],
                  _mtxFee = modelCoin 100_000_000_000,
                  _mtxDCert =
                    [ ModelRegisterStake stakeAddr,
                      ModelRegisterPool modelPool,
                      ModelDelegate (ModelDelegation stakeAddr "pool1")
                    ]
                }
            ]
        ]
      oneAtATime =
        [ ModelBlock
            0
            [ modelTx
                { _mtxInputs = Set.fromList [0],
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
                  _mtxOutputs =
                    [ (2, modelTxOut "unstaked" (modelCoin 9_850_000_000_000))
                    ],
                  _mtxFee = modelCoin 25_000_000_000,
                  _mtxDCert = [ModelRegisterStake stakeAddr]
                }
            ],
          ModelBlock
            2
            [ modelTx
                { _mtxInputs = Set.fromList [2],
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
                  _mtxCollateral = SupportsPlutus $ Set.fromList [x | x <- [3], needsCollateral],
                  _mtxOutputs =
                    [ (100, modelTxOut "unstaked" (modelCoin 9_800_000_000_000))
                    ],
                  _mtxFee = modelCoin 25_000_000_000,
                  _mtxDCert =
                    [ ModelDelegate (ModelDelegation stakeAddr "pool1")
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

      unStake =
        [ ModelBlock
            0
            [ modelTx
                { _mtxInputs = Set.fromList [101],
                  _mtxCollateral = SupportsPlutus $ Set.fromList [x | x <- [100], needsCollateral],
                  _mtxOutputs =
                    [ (102, modelTxOut "unstaked" (modelCoin 75_000_000_000))
                    ],
                  _mtxFee = modelCoin 25_000_000_000,
                  _mtxDCert =
                    [ ModelDelegate (ModelDelegation stakeAddr "pool1")
                    ]
                }
            ]
        ]

      go reg =
        testChainModelInteractionWith
          proxy
          checkAllWithdrawnRewards
          genAct
          [ ModelEpoch reg (ModelBlocksMade $ Map.fromList []),
            ModelEpoch unStake (ModelBlocksMade $ Map.fromList []),
            ModelEpoch [] (ModelBlocksMade $ Map.fromList [("pool1", 1 % 1)]),
            ModelEpoch [] (ModelBlocksMade $ Map.fromList []),
            ModelEpoch
              [ ModelBlock
                  0
                  [ modelTx
                      { _mtxInputs = Set.fromList [100],
                        _mtxCollateral = SupportsPlutus $ Set.fromList [x | x <- [100], needsCollateral],
                        _mtxOutputs =
                          [ (103, modelTxOut "unstaked" (modelCoin 9_700_000_000_000)),
                            (104, modelTxOut "reward-less-minimum" (modelReward stakeAddr $- modelCoin 100_000_000)),
                            (105, modelTxOut "minimum" (modelCoin 100_000_000))
                          ],
                        _mtxFee = modelCoin 100_000_000_000,
                        _mtxWdrl = modelRewards [stakeAddr]
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
    ( [(ModelUTxOId, ModelAddress (ScriptFeature era), Coin)],
      [ModelEpoch AllModelFeatures]
    )
genModel' _ globals = do
  (a, b) <-
    genModel @era globals $
      defaultGenActionContext
        { -- TODO: solve "zero withdrawal" issue, which is that some model
          -- generated withdrawals correspond to zero rewards (esp in alonzo).
          -- These numbers are chosen so that the "zero withdrawal" issue occurs
          -- rarely.
          _genActionContexts_epochs = choose (10, 18),
          _genActionContexts_txnsPerSlot = frequency [(1, pure 1), (10, choose (2, 15))],
          _genActionContexts_numSlotsUsed = choose (2, 15)
        }
  pure (a, maybe (error "fromJust") id $ traverse (filterFeatures $ FeatureTag ValueFeatureTag_AnyOutput $ ScriptFeatureTag_PlutusV1) b)

simulateChainModel ::
  (KnownScriptFeature (ScriptFeature era)) =>
  [(ModelUTxOId, ModelAddress (ScriptFeature era), Coin)] ->
  [ModelEpoch era] ->
  ModelLedger era
simulateChainModel g e =
  flip State.execState (mkModelLedger g) $
    for_ e $ \mepoch -> do
      State.modify (applyModelEpoch mepoch)

prop_simulateChainModel ::
  Testable prop =>
  [(ModelUTxOId, ModelAddress sf, Coin)] ->
  [ModelEpoch AllModelFeatures] ->
  prop ->
  Property
prop_simulateChainModel g e = execPropertyWriter $ do
  Writer.tell $ Endo $ counterexample ("genesis:\t" <> show g)
  ((), st') :: ((), ModelLedger AllModelFeatures) <- flip
    State.runStateT
    (mkModelLedger $ over (traverse . _2) liftModelAddress' g)
    $ for_ e $ \mepoch -> do
      st <- State.get
      tellProperty $ counterexample ("ledger:\t" <> show st)
      tellProperty $ counterexample ("epoch:\t" <> show mepoch)
      State.modify (applyModelEpoch mepoch)
  tellProperty $ counterexample ("final ledger state:" <> show st')

tellProperty :: Writer.MonadWriter (Endo Property) m => (Property -> Property) -> m ()
tellProperty = Writer.tell . Endo

execPropertyWriter :: Testable prop => Writer.Writer (Endo Property) () -> prop -> Property
execPropertyWriter x k = (flip appEndo (property k)) . Writer.execWriter $ x

execPropertyWriter_ :: Writer.Writer (Endo Property) () -> Property
execPropertyWriter_ x = (flip appEndo (property True)) . Writer.execWriter $ x

checkElaboratorResult :: LedgerState.NewEpochState era -> EraElaboratorState era -> Property
checkElaboratorResult _nes ees = execPropertyWriter_ $ do
  let stats = (_eesStats ees)
  tellProperty $ counterexample $ (<>) "stats:" $ show stats
  -- tellProperty $ cover 90 (_eeStats_badWdrls stats * 10 <= _eeStats_wdrls stats) "zero withdrawals < 10%"
  tellProperty $ cover 50 (_eeStats_badWdrls stats <= 0) "zero withdrawals"
  pure ()

data ModelStats f = ModelStats
  { _numberOfEpochs :: f Int,
    _numberOfTransactions :: f Int,
    _numberOfCerts :: f Int,
    _blocksMade :: f Rational,
    _numberOfDelegations :: f Int,
    _withdrawals :: f Int
  }
  deriving (Generic)

deriving instance
  ( Show (f Rational),
    Show (f Int)
  ) =>
  Show (ModelStats f)

instance FFunctor ModelStats where ffmap = ffmapDefault

instance FZip ModelStats where fzipWith = gfzipWith

instance FRepeat ModelStats where frepeat = gfrepeat

instance FFoldable ModelStats where ffoldMap = ffoldMapDefault

instance FTraversable ModelStats where ftraverse = gftraverse

mstats :: ModelStats ((->) [ModelEpoch era])
mstats =
  ModelStats
    { _numberOfEpochs = (lengthOf (traverse)),
      _numberOfTransactions = (lengthOf (traverse . modelTxs)),
      _numberOfCerts = (lengthOf (traverse . modelDCerts)),
      _blocksMade = (sumOf (traverse . modelEpoch_blocksMade . _ModelBlocksMade . traverse)),
      _numberOfDelegations = (lengthOf (traverse . modelDCerts . _ModelDelegate)),
      _withdrawals = (lengthOf (traverse . modelTxs . modelTx_wdrl . traverse))
    }

mstatsCover :: ModelStats (Const (Double, String) :*: Predicate)
mstatsCover =
  ModelStats
    { _numberOfEpochs = Const (90, "number of epochs") :*: Predicate (> 5),
      _numberOfTransactions = Const (90, "number of transactions") :*: Predicate (> 5),
      _numberOfCerts = Const (50, "number of certs") :*: Predicate (> 5),
      _blocksMade = Const (50, "blocks made") :*: Predicate (> 2.5),
      _numberOfDelegations = Const (10, "number of delegation") :*: Predicate (> 5),
      _withdrawals = Const (10, "withdrawals") :*: Predicate (> 5)
    }

propModelStats ::
  Testable prop =>
  -- [(ModelUTxOId, ModelAddress (ScriptFeature era), Coin)] ->
  [ModelEpoch era] ->
  prop ->
  Property
propModelStats epochs =
  execPropertyWriter $
    ffor_ (fzipWith (:*:) mstats mstatsCover) $ \(f :*: (Const (pct, tag) :*: Predicate threshhold)) ->
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
    Show (Core.Value era)
  ) =>
  proxy era ->
  Property
modelGenTest proxy =
  forAllShrink (genModel' (reifyRequiredFeatures $ Proxy @(EraFeatureSet era)) testGlobals) (const []) $ \(a, b) ->
    ( execPropertyWriter $ do
        tellProperty $ counterexample ("numPools: " <> show (lengthOf (traverse . modelDCerts . _ModelDelegate) b))
        tellProperty $ propModelStats b
        -- tellProperty $ prop_simulateChainModel a b
    )
      (testChainModelInteractionWith proxy checkElaboratorResult a b)

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
  (a, b) <- time "generate" $ generate $ genModel' proxy' testGlobals
  time "examine" $ print $ examineModel b
  _mresult <- time "modelApp" $ pure $ simulateChainModel a b
  result <- time "elaborate" $ pure $ fst $ chainModelInteractionWith proxy a b
  print result

shrinkModelTransactions ::
  [ModelTx era] ->
  [[ModelTx era]]
shrinkModelTransactions txns = List.inits txns

newPrevList ::
  [a] ->
  [a] ->
  [a]
newPrevList [] prevA = prevA
newPrevList a prevA = prevA <> ((:) (List.last a) [])

shrinkModelBlocks ::
  [ModelBlock era] ->
  [ModelBlock era] ->
  [[ModelBlock era]]
shrinkModelBlocks [] _ = []
shrinkModelBlocks ((ModelBlock slotNo txns) : blocks) prevBlocks =
  let currentBlockPrefixes = (ModelBlock slotNo) <$> (shrinkModelTransactions txns)
      currentBPrefixList = (flip (:) []) <$> currentBlockPrefixes
      allBlockPrefixes = ((<>) prevBlocks) <$> currentBPrefixList
  in allBlockPrefixes <> (shrinkModelBlocks blocks $ newPrevList currentBlockPrefixes prevBlocks)

shrinkModelEpochs ::
  [ModelEpoch AllModelFeatures] ->
  [ModelEpoch AllModelFeatures] ->
  [[ModelEpoch AllModelFeatures]]
shrinkModelEpochs [] _ = []
shrinkModelEpochs ((ModelEpoch blocks blocksMade) : epochs) prevEpochs =
  let currentEpochPrefixes = (flip ModelEpoch blocksMade) <$> (shrinkModelBlocks blocks [])
      currentEpochPrefixList = (flip (:) []) <$> currentEpochPrefixes
      allEpochPrefixes = ((<>) prevEpochs) <$> currentEpochPrefixList
  in allEpochPrefixes <> (shrinkModelEpochs epochs $ newPrevList currentEpochPrefixes prevEpochs)

shrinkModelSimple
  :: forall a.
      (a, [ModelEpoch AllModelFeatures])
  -> [(a, [ModelEpoch AllModelFeatures])]
shrinkModelSimple (genesis, epochs) = (,) genesis <$> (List.init $ shrinkModelEpochs epochs [])

-- | some hand-written model based unit tests
modelUnitTests ::
  forall era proxy.
  ( ElaborateEraModel era,
    Default (AdditionalGenesisConfig era),
    Eq (PredicateFailure (Core.EraRule "LEDGER" era)),
    Show (PredicateFailure (Core.EraRule "LEDGER" era)),
    Show (Core.Value era)
  ) =>
  proxy era ->
  TestTree
modelUnitTests proxy =
  testGroup
    (show $ typeRep proxy)
    [ testProperty "gen" $ checkCoverage $ modelGenTest proxy,
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
      testGroup "deleg-plutus" $ modelTestDelegations proxy True (ModelScriptAddress $ ModelPlutusScript_AlwaysSucceeds 4),
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
                        _mtxFee = modelCoin 1_000_000
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
                        _mtxOutputs =
                          [ (1, modelTxOut "bob" (modelCoin 100_000_000)),
                            ( 2,
                              (modelTxOut (ModelScriptAddress $ ModelPlutusScript_AlwaysSucceeds 2) (modelCoin 1_000_000_000 $- (modelCoin 100_000_000 $+ modelCoin 1_000_000)))
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

modelUnitTests_ :: TestTree
modelUnitTests_ =
  testGroup
    "model-unit-tests"
    [ modelUnitTests (Proxy :: Proxy (ShelleyEra C_Crypto)),
      modelUnitTests (Proxy :: Proxy (AlonzoEra C_Crypto))
    ]

modelTxOut :: ModelAddress AllScriptFeatures -> ModelValue 'ExpectAnyOutput AllModelFeatures -> ModelTxOut AllModelFeatures
modelTxOut a v = ModelTxOut a v (SupportsPlutus dh)
  where
    dh = case a of
      ModelAddress _ -> Nothing
      ModelScriptAddress _ -> Just $ PlutusTx.I 42

defaultTestMain :: IO ()
defaultTestMain = defaultMain modelUnitTests_
