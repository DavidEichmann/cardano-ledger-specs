{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE EmptyDataDeriving #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Test.Cardano.Ledger.ModelChain where

import Cardano.Ledger.BaseTypes
import Cardano.Ledger.Coin
import qualified Cardano.Ledger.Crypto as C
import Cardano.Ledger.Mary.Value (AssetName, PolicyID (..))
import qualified Cardano.Ledger.Mary.Value
import qualified Cardano.Ledger.Val as Val
import Cardano.Slotting.Slot hiding (at)
import Control.Applicative
import Control.Arrow ((&&&))
import Control.DeepSeq
import Control.Lens
import Control.Monad
import qualified Control.Monad.State.Strict as State
import Data.Foldable (fold, for_)
import Data.Group
import Data.Kind (Type)
import qualified Data.List as List
import qualified Data.Map as Map
import Data.Proxy
import Data.Semigroup (Sum (..))
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Traversable
import qualified GHC.Exts as GHC
import GHC.Generics (Generic)
import qualified PlutusTx
import Quiet (Quiet (..))
import Shelley.Spec.Ledger.STS.EraMapping ()
import Test.Cardano.Ledger.ModelChain.Address
import Test.Cardano.Ledger.ModelChain.FeatureSet
import Test.Cardano.Ledger.ModelChain.Script
import Test.Cardano.Ledger.ModelChain.Value

class Val.Val val => ValueFromList val crypto | val -> crypto where
  valueFromList :: Integer -> [(PolicyID crypto, AssetName, Integer)] -> val

  insert :: (Integer -> Integer -> Integer) -> PolicyID crypto -> AssetName -> Integer -> val -> val

  gettriples :: val -> (Integer, [(PolicyID crypto, AssetName, Integer)])

instance C.Crypto crypto => ValueFromList (Cardano.Ledger.Mary.Value.Value crypto) crypto where
  valueFromList = Cardano.Ledger.Mary.Value.valueFromList

  insert = Cardano.Ledger.Mary.Value.insert

  gettriples (Cardano.Ledger.Mary.Value.Value c m1) = (c, triples)
    where
      triples =
        [ (policyId, aname, amount)
          | (policyId, m2) <- Map.toList m1,
            (aname, amount) <- Map.toList m2
        ]

-- TODO: this is a bit overconstrained, we probably want a more constraints
-- based approach using ValueFromList
type family ElaborateValueType (valF :: TyValueExpected) crypto :: Type where
  ElaborateValueType 'ExpectAdaOnly _ = Coin
  ElaborateValueType 'ExpectAnyOutput crypto = Cardano.Ledger.Mary.Value.Value crypto

instance RequiredFeatures ModelTxOut where
  filterFeatures tag@(FeatureTag v _) (ModelTxOut addr qty dat) =
    hasKnownValueFeature v $
      ModelTxOut
        <$> filterModelAddress tag addr
        <*> (filterFeatures tag =<< filterModelValue qty)
        <*> (filterSupportsPlutus tag dat)

filterModelValueVars ::
  forall a b c d.
  (KnownRequiredFeatures c, KnownValueFeature d) =>
  ModelValueVars a b ->
  Maybe (ModelValueVars c d)
filterModelValueVars (ModelValue_Reward x) = ModelValue_Reward <$> filterModelAddress (reifyRequiredFeatures (Proxy @c)) x
filterModelValueVars (ModelValue_MA ys) = do
  Refl <- reifyExpectAnyOutput (reifyValueFeature (Proxy @d))
  Refl <- reifyExpectAnyOutput (reifyValueFeature (Proxy @(ValueFeature c)))

  let f :: ModelScript (ScriptFeature a) -> Maybe (ModelScript (ScriptFeature c))
      f = \case
        ModelScript_Timelock t -> case reifyScriptFeature (Proxy @(ScriptFeature c)) of
          ScriptFeatureTag_None -> Nothing
          ScriptFeatureTag_Simple -> Just $ ModelScript_Timelock t
          ScriptFeatureTag_PlutusV1 -> Just $ ModelScript_Timelock t
        ModelScript_PlutusV1 t -> case reifyScriptFeature (Proxy @(ScriptFeature c)) of
          ScriptFeatureTag_None -> Nothing
          ScriptFeatureTag_Simple -> Nothing
          ScriptFeatureTag_PlutusV1 -> Just $ ModelScript_PlutusV1 t

  ModelValue_MA <$> _1 f ys

-- change the "expected return type" of a ModelValue
filterModelValue ::
  forall a b c.
  (KnownValueFeature b, KnownRequiredFeatures c) =>
  ModelValue a c ->
  Maybe (ModelValue b c)
filterModelValue = \case
  ModelValue x -> ModelValue <$> traverse filterModelValueVars x

instance KnownValueFeature v => RequiredFeatures (ModelValue v) where
  filterFeatures tag (ModelValue val) = ModelValue <$> traverse (hasKnownRequiredFeatures tag filterModelValueVars) val

instance RequiredFeatures ModelTx where
  filterFeatures :: forall a b. KnownRequiredFeatures a => FeatureTag b -> ModelTx a -> Maybe (ModelTx b)
  filterFeatures tag (ModelTx ins outs fee dcert wdrl g cins) =
    ModelTx ins
      <$> (traverse . traverse) (filterFeatures tag) outs
      <*> (filterFeatures tag fee)
      <*> traverse (filterFeatures tag) dcert
      <*> fmap Map.fromList (for (Map.toList wdrl) $ \(k, v) -> (,) <$> filterModelAddress tag k <*> filterFeatures tag v) -- traverse (filterFeatures tag) f
      <*> case g of
        NoMintSupport () -> case tag of
          FeatureTag ValueFeatureTag_AdaOnly _ -> pure $ NoMintSupport ()
          FeatureTag ValueFeatureTag_AnyOutput _ -> pure (SupportsMint . ModelValue . ModelValue_Inject $ Coin 0)
        SupportsMint g' -> case tag of
          FeatureTag ValueFeatureTag_AdaOnly _ | g' == ModelValue (ModelValue_Inject $ Val.zero) -> pure $ NoMintSupport ()
          FeatureTag ValueFeatureTag_AdaOnly _ -> Nothing
          FeatureTag ValueFeatureTag_AnyOutput _ -> SupportsMint <$> filterFeatures tag g'
      <*> let setNotEmpty :: Set x -> Maybe (Set x)
              setNotEmpty x
                | Set.null x = Nothing
                | otherwise = Just x
           in (fmap (mapSupportsPlutus fold) $ filterSupportsPlutus tag $ mapSupportsPlutus setNotEmpty cins)

filterModelAddress ::
  FeatureTag b ->
  ModelAddress a ->
  Maybe (ModelAddress (ScriptFeature b))
filterModelAddress (FeatureTag _ s) = \case
  ModelAddress a -> Just (ModelAddress a)
  ModelScriptAddress a -> case s of
    ScriptFeatureTag_None -> Nothing
    ScriptFeatureTag_Simple -> Nothing
    ScriptFeatureTag_PlutusV1 -> Just (ModelScriptAddress a)

instance RequiredFeatures ModelBlock where
  filterFeatures tag (ModelBlock slotNo txns) =
    ModelBlock slotNo
      <$> traverse (filterFeatures tag) txns

instance RequiredFeatures ModelEpoch where
  filterFeatures tag (ModelEpoch blocks x) =
    ModelEpoch
      <$> traverse (filterFeatures tag) blocks
      <*> pure x

type ModelMA era = (ModelScript era, AssetName)

data ModelValueVars era (k :: TyValueExpected) where
  ModelValue_Reward :: ModelAddress (ScriptFeature era) -> ModelValueVars era k
  ModelValue_MA ::
    ('ExpectAnyOutput ~ ValueFeature era) =>
    ModelMA (ScriptFeature era) ->
    ModelValueVars era 'ExpectAnyOutput

instance NFData (ModelValueVars era k) where
  rnf = \case
    ModelValue_Reward a -> rnf a
    ModelValue_MA a -> rnf a

deriving instance Show (ModelValueVars era valF)

deriving instance Eq (ModelValueVars era valF)

deriving instance Ord (ModelValueVars era valF)

newtype ModelValue k era = ModelValue {unModelValue :: ModelValueF (ModelValueVars era k)}
  deriving (Eq, Ord, Generic, NFData)
  deriving (Show) via Quiet (ModelValue k era)

modelValueInject :: Coin -> ModelValue k era
modelValueInject = ModelValue . ModelValue_Inject

instance Semigroup (ModelValue k era) where
  ModelValue x <> ModelValue y = ModelValue (x `ModelValue_Add` y)

instance Monoid (ModelValue k era) where
  mempty = modelValueInject $ Coin 0

data ModelTxOut era = ModelTxOut
  { _mtxo_address :: !(ModelAddress (ScriptFeature era)),
    _mtxo_value :: !(ModelValue (ValueFeature era) era),
    _mtxo_data :: !(IfSupportsPlutus () (Maybe PlutusTx.Data) (ScriptFeature era))
  }
  deriving (Eq, Ord, Generic)
  deriving (Show) via Quiet (ModelTxOut era)

instance NFData (ModelTxOut era)

modelTxOut_address :: forall era. Lens' (ModelTxOut era) (ModelAddress (ScriptFeature era))
modelTxOut_address = lens _mtxo_address (\s b -> s {_mtxo_address = b})
{-# INLINE modelTxOut_address #-}

modelTxOut_value :: Lens' (ModelTxOut era) (ModelValue (ValueFeature era) era)
modelTxOut_value = lens _mtxo_value (\s b -> s {_mtxo_value = b})
{-# INLINE modelTxOut_value #-}

modelTxOut_data :: Lens' (ModelTxOut era) (IfSupportsPlutus () (Maybe PlutusTx.Data) (ScriptFeature era))
modelTxOut_data = lens _mtxo_data (\s b -> s {_mtxo_data = b})
{-# INLINE modelTxOut_data #-}

newtype ModelUTxOId = ModelUTxOId {unModelUTxOId :: Integer}
  deriving (Eq, Ord, Num, Enum, Generic, NFData)

instance Show ModelUTxOId where
  showsPrec n (ModelUTxOId x) = showsPrec n x

data ModelTx (era :: FeatureSet) = ModelTx
  { _mtxInputs :: !(Set ModelUTxOId),
    _mtxOutputs :: ![(ModelUTxOId, ModelTxOut era)],
    _mtxFee :: !(ModelValue 'ExpectAdaOnly era),
    _mtxDCert :: ![ModelDCert era],
    _mtxWdrl :: !(Map.Map (ModelAddress (ScriptFeature era)) (ModelValue 'ExpectAdaOnly era)),
    _mtxMint :: !(IfSupportsMint () (ModelValue (ValueFeature era) era) (ValueFeature era)),
    _mtxCollateral :: !(IfSupportsPlutus () (Set ModelUTxOId) (ScriptFeature era))
  }
  deriving (Show, Generic, Eq)

instance NFData (ModelTx era)

class HasModelTx era a | a -> era where
  modelTxs :: Traversal' a (ModelTx era)

instance HasModelTx era (ModelTx era) where
  modelTxs = id
  {-# INLINE modelTxs #-}

instance HasModelDCert era (ModelTx era) where
  modelDCerts = modelTx_dCert . traverse
  {-# INLINE modelDCerts #-}

modelTx_inputs :: Lens' (ModelTx era) (Set ModelUTxOId)
modelTx_inputs = lens _mtxInputs (\s b -> s {_mtxInputs = b})
{-# INLINE modelTx_inputs #-}

modelTx_outputs :: Lens' (ModelTx era) [(ModelUTxOId, ModelTxOut era)]
modelTx_outputs = lens _mtxOutputs (\s b -> s {_mtxOutputs = b})
{-# INLINE modelTx_outputs #-}

-- focus on a specified output with the given id;
modelTx_outputAt :: ModelUTxOId -> Lens' (ModelTx era) (Maybe (ModelTxOut era))
modelTx_outputAt k = modelTx_outputs . lens (List.lookup k) (flip f)
  where
    f :: forall a. Maybe a -> [(ModelUTxOId, a)] -> [(ModelUTxOId, a)]
    f = \case
      Nothing ->
        let g [] = []
            g ((k', v) : rest) = if k == k' then rest else (k', v) : g rest
         in g
      Just v' ->
        let h [] = [(k, v')]
            h ((k', v) : rest) = if k == k' then (k, v') : rest else (k', v) : h rest
         in h
{-# INLINE modelTx_outputAt #-}

modelTx_fee :: Lens' (ModelTx era) (ModelValue 'ExpectAdaOnly era)
modelTx_fee = lens _mtxFee (\s b -> s {_mtxFee = b})
{-# INLINE modelTx_fee #-}

modelTx_dCert :: Lens' (ModelTx era) [ModelDCert era]
modelTx_dCert = lens _mtxDCert (\s b -> s {_mtxDCert = b})
{-# INLINE modelTx_dCert #-}

modelTx_wdrl :: Lens' (ModelTx era) (Map.Map (ModelAddress (ScriptFeature era)) (ModelValue 'ExpectAdaOnly era))
modelTx_wdrl = lens _mtxWdrl (\s b -> s {_mtxWdrl = b})
{-# INLINE modelTx_wdrl #-}

modelTx_mint :: Lens' (ModelTx era) (IfSupportsMint () (ModelValue (ValueFeature era) era) (ValueFeature era))
modelTx_mint = lens _mtxMint (\s b -> s {_mtxMint = b})
{-# INLINE modelTx_mint #-}

modelTx_collateral :: Lens' (ModelTx era) (IfSupportsPlutus () (Set ModelUTxOId) (ScriptFeature era))
modelTx_collateral = lens _mtxCollateral (\s b -> s {_mtxCollateral = b})
{-# INLINE modelTx_collateral #-}

data ModelBlock era = ModelBlock
  { _modelBlock_slot :: SlotNo,
    _modelBlock_txSeq :: [ModelTx era]
  }
  deriving (Show, Generic, Eq)

instance NFData (ModelBlock era)

instance HasModelDCert era (ModelBlock era) where
  modelDCerts = modelBlock_txSeq . traverse . modelDCerts
  {-# INLINE modelDCerts #-}

instance HasModelTx era (ModelBlock era) where
  modelTxs = modelBlock_txSeq . traverse
  {-# INLINE modelTxs #-}

modelBlock_slot :: Lens' (ModelBlock era) SlotNo
modelBlock_slot = lens _modelBlock_slot (\s b -> s {_modelBlock_slot = b})
{-# INLINE modelBlock_slot #-}

modelBlock_txSeq :: Lens' (ModelBlock era) [ModelTx era]
modelBlock_txSeq = lens _modelBlock_txSeq (\s b -> s {_modelBlock_txSeq = b})
{-# INLINE modelBlock_txSeq #-}

newtype ModelPoolId = ModelPoolId {unModelPoolId :: String}
  deriving (Eq, Ord, GHC.IsString, NFData)

instance Show ModelPoolId where
  showsPrec n (ModelPoolId x) = showsPrec n x

newtype ModelBlocksMade = ModelBlocksMade {unModelBlocksMade :: Map.Map ModelPoolId Rational}
  deriving (Generic, NFData, Eq)
  deriving (Show) via Quiet ModelBlocksMade
  deriving (Semigroup) via GrpMap ModelPoolId (Sum Rational)
  deriving (Monoid) via GrpMap ModelPoolId (Sum Rational)

_ModelBlocksMade :: Iso' ModelBlocksMade (Map.Map ModelPoolId Rational)
_ModelBlocksMade = iso unModelBlocksMade ModelBlocksMade

repartition :: forall a b t. (Traversable t, Integral a, RealFrac b) => a -> t b -> t a
repartition total weights = State.evalState (traverse step weights) (0 :: b)
  where
    step weight = do
      err <- State.get
      let fracValue :: b
          fracValue = err + fromIntegral total * weight
          value :: a
          value = round fracValue
      State.put (fracValue - fromIntegral value)
      pure value

-- TODO: explicit Epoch.
data ModelEpoch era = ModelEpoch
  { _modelEpoch_blocks :: [ModelBlock era],
    _modelEpoch_blocksMade :: ModelBlocksMade
  }
  deriving (Show, Generic, Eq)

instance NFData (ModelEpoch era)

instance HasModelDCert era (ModelEpoch era) where
  modelDCerts = modelEpoch_blocks . traverse . modelDCerts
  {-# INLINE modelDCerts #-}

instance HasModelTx era (ModelEpoch era) where
  modelTxs = modelEpoch_blocks . traverse . modelTxs
  {-# INLINE modelTxs #-}

modelEpoch_blocks :: Lens' (ModelEpoch era) [ModelBlock era]
modelEpoch_blocks = lens _modelEpoch_blocks (\s b -> s {_modelEpoch_blocks = b})
{-# INLINE modelEpoch_blocks #-}

modelEpoch_blocksMade :: Lens' (ModelEpoch era) ModelBlocksMade
modelEpoch_blocksMade = lens _modelEpoch_blocksMade (\s b -> s {_modelEpoch_blocksMade = b})
{-# INLINE modelEpoch_blocksMade #-}

data ModelDelegation era = ModelDelegation
  { _mdDelegator :: !(ModelAddress (ScriptFeature era)),
    _mdDelegatee :: !ModelPoolId
  }
  deriving (Generic, Eq, Ord)
  deriving (Show) via Quiet (ModelDelegation era)

instance NFData (ModelDelegation era)

instance RequiredFeatures ModelDelegation where
  filterFeatures tag (ModelDelegation a b) =
    ModelDelegation
      <$> filterModelAddress tag a
      <*> pure b

data ModelPoolParams era = ModelPoolParams
  { _mppId :: !ModelPoolId,
    _mppPledge :: !Coin,
    _mppCost :: !Coin,
    _mppMargin :: !UnitInterval,
    _mppRAcnt :: !(ModelAddress (ScriptFeature era)),
    _mppOwners :: ![ModelAddress (ScriptFeature era)]
  }
  deriving (Show, Eq, Ord, Generic)

instance NFData (ModelPoolParams era)

instance RequiredFeatures ModelPoolParams where
  filterFeatures tag (ModelPoolParams poolId pledge cost margin rAcnt owners) =
    ModelPoolParams poolId pledge cost margin
      <$> filterModelAddress tag rAcnt
      <*> traverse (filterModelAddress tag) owners

-- ignores genesis delegation details.
data ModelDCert era
  = ModelRegisterStake (ModelAddress (ScriptFeature era))
  | ModelDeRegisterStake (ModelAddress (ScriptFeature era))
  | ModelDelegate (ModelDelegation era)
  | ModelRegisterPool (ModelPoolParams era)
  | ModelRetirePool ModelPoolId EpochNo
  deriving (Show, Generic, Eq)

instance NFData (ModelDCert era)

_ModelRegisterStake :: Prism' (ModelDCert era) (ModelAddress (ScriptFeature era))
_ModelRegisterStake = prism ModelRegisterStake $ \case
  ModelRegisterStake x -> Right x
  x -> Left x
{-# INLINE _ModelRegisterStake #-}

_ModelDeRegisterStake :: Prism' (ModelDCert era) (ModelAddress (ScriptFeature era))
_ModelDeRegisterStake = prism ModelDeRegisterStake $ \case
  ModelDeRegisterStake x -> Right x
  x -> Left x
{-# INLINE _ModelDeRegisterStake #-}

_ModelDelegate :: Prism' (ModelDCert era) (ModelDelegation era)
_ModelDelegate = prism ModelDelegate $ \case
  ModelDelegate x -> Right x
  x -> Left x
{-# INLINE _ModelDelegate #-}

_ModelRegisterPool :: Prism' (ModelDCert era) (ModelPoolParams era)
_ModelRegisterPool = prism ModelRegisterPool $ \case
  ModelRegisterPool x -> Right x
  x -> Left x
{-# INLINE _ModelRegisterPool #-}

_ModelRetirePool :: Prism' (ModelDCert era) (ModelPoolId, EpochNo)
_ModelRetirePool = prism (uncurry ModelRetirePool) $ \case
  ModelRetirePool x y -> Right (x, y)
  x -> Left x
{-# INLINE _ModelRetirePool #-}

class HasModelDCert era a | a -> era where
  modelDCerts :: Traversal' a (ModelDCert era)

instance HasModelDCert era (ModelDCert era) where
  modelDCerts = id
  {-# INLINE modelDCerts #-}

instance RequiredFeatures ModelDCert where
  filterFeatures tag = \case
    ModelRegisterStake a -> ModelRegisterStake <$> filterModelAddress tag a
    ModelDeRegisterStake a -> ModelDeRegisterStake <$> filterModelAddress tag a
    ModelDelegate a -> ModelDelegate <$> filterFeatures tag a
    ModelRegisterPool a -> ModelRegisterPool <$> filterFeatures tag a
    ModelRetirePool a b -> pure $ ModelRetirePool a b

-- TODO: | ModelMIRCert Shelley.MIRPot (Map.Map ModelAddress DeltaCoin)

data ModelPredicateFailure era
  = ModelValueNotConservedUTxO
      !(ModelValue (ValueFeature era) era)
      -- ^ the Coin consumed by this transaction
      !(ModelValue (ValueFeature era) era)
      -- ^ the Coin produced by this transaction

type ModelLedgerInputs era =
  ( [(ModelUTxOId, ModelAddress (ScriptFeature era), Coin)],
    [ModelEpoch era]
  )

data ModelSnapshot era = ModelSnapshot
  { _modelSnapshot_stake :: Map.Map (ModelAddress (ScriptFeature era)) (ModelUtxoMap era, ModelTxNo),
    _modelSnapshot_delegations :: Map.Map (ModelAddress (ScriptFeature era)) (ModelPoolId, ModelTxNo),
    _modelSnapshot_pools :: Map.Map ModelPoolId (ModelPoolParams era, ModelTxNo)
  }
  deriving (Eq, Generic)
  deriving (Show) via Quiet (ModelSnapshot era)

instance NFData (ModelSnapshot era)

emptyModelSnapshot :: ModelSnapshot era
emptyModelSnapshot = ModelSnapshot Map.empty Map.empty Map.empty

modelSnapshot_stake :: Lens' (ModelSnapshot era) (Map.Map (ModelAddress (ScriptFeature era)) (ModelUtxoMap era, ModelTxNo))
modelSnapshot_stake a2fb s = (\b -> s {_modelSnapshot_stake = b}) <$> a2fb (_modelSnapshot_stake s)
{-# INLINE modelSnapshot_stake #-}

modelSnapshot_delegations :: Lens' (ModelSnapshot era) (Map.Map (ModelAddress (ScriptFeature era)) (ModelPoolId, ModelTxNo))
modelSnapshot_delegations a2fb s = (\b -> s {_modelSnapshot_delegations = b}) <$> a2fb (_modelSnapshot_delegations s)
{-# INLINE modelSnapshot_delegations #-}

modelSnapshot_pools :: Lens' (ModelSnapshot era) (Map.Map ModelPoolId (ModelPoolParams era, ModelTxNo))
modelSnapshot_pools a2fb s = (\b -> s {_modelSnapshot_pools = b}) <$> a2fb (_modelSnapshot_pools s)
{-# INLINE modelSnapshot_pools #-}

data ModelUtxoMap era = ModelUtxoMap
  { _modelUtxoMap_utxos :: (Map.Map ModelUTxOId (Coin, ModelTxOut era)),
    _modelUtxoMap_balances :: GrpMap (ModelAddress (ScriptFeature era)) Coin
  }
  deriving (Eq, Show, Generic)

instance Semigroup (ModelUtxoMap era) where
  ModelUtxoMap utxos stake <> ModelUtxoMap utxos' stake' =
    ModelUtxoMap
      (Map.unionWith (\x y -> if x == y then x else error $ unwords ["unmergable ModelUtxoMap:", show x, "/=", show y]) utxos utxos')
      (stake <> stake')

instance Monoid (ModelUtxoMap era) where
  mempty = ModelUtxoMap Map.empty mempty

mkModelUtxoMap ::
  forall era.
  KnownScriptFeature (ScriptFeature era) =>
  [(ModelUTxOId, ModelAddress (ScriptFeature era), Coin)] ->
  ModelUtxoMap era
mkModelUtxoMap = (.) (uncurry ModelUtxoMap) $
  foldMap $ \(ui, ma, val) ->
    ( Map.singleton ui (val, ModelTxOut ma (modelValueInject val) dh),
      grpMapSingleton ma val
    )
  where
    dh = ifSupportsPlutus (Proxy :: Proxy (ScriptFeature era)) () Nothing

getBal :: Map.Map ModelUTxOId (Coin, ModelTxOut era) -> GrpMap (ModelAddress (ScriptFeature era)) Coin
getBal = foldMap (\(val, txo) -> grpMapSingleton (_mtxo_address txo) val)

getModelValueCoin :: ModelValue a c -> Coin
getModelValueCoin = foldMap Val.coin . evalModelValueSimple . unModelValue

spendModelUTxOs ::
  Set ModelUTxOId ->
  [(ModelUTxOId, ModelTxOut era)] ->
  ModelUtxoMap era ->
  ModelUtxoMap era
spendModelUTxOs ins outs xs =
  let ins' = Map.restrictKeys (_modelUtxoMap_utxos xs) ins
      outs' = Map.fromList $ (fmap . fmap) (getModelValueCoin . _mtxo_value &&& id) outs
   in ModelUtxoMap
        { _modelUtxoMap_utxos = Map.withoutKeys (_modelUtxoMap_utxos xs `Map.union` outs') ins,
          _modelUtxoMap_balances = _modelUtxoMap_balances xs <> getBal outs' ~~ getBal ins'
        }

instance NFData (ModelUtxoMap era)

type instance Index (ModelUtxoMap era) = ModelUTxOId

type instance IxValue (ModelUtxoMap era) = ModelTxOut era

instance Ixed (ModelUtxoMap era)

instance At (ModelUtxoMap era) where
  at :: ModelUTxOId -> Lens' (ModelUtxoMap era) (Maybe (ModelTxOut era))
  at k = \a2fb s ->
    let a = Map.lookup k $ _modelUtxoMap_utxos s
        b2t :: Maybe (ModelTxOut era) -> ModelUtxoMap era
        b2t b =
          let val = foldMap (getModelValueCoin . _mtxo_value) b
           in ModelUtxoMap
                { _modelUtxoMap_utxos = set (at k) (fmap ((,) val) b) (_modelUtxoMap_utxos s),
                  _modelUtxoMap_balances =
                    _modelUtxoMap_balances s
                      <> foldMap (\(val', ui) -> grpMapSingleton (_mtxo_address ui) (invert val')) a
                      <> foldMap (\ui -> grpMapSingleton (_mtxo_address ui) val) b
                }
     in b2t <$> (a2fb $ fmap snd a)

newtype ModelTxNo = ModelTxNo {unModelTxNo :: Integer}
  deriving (Eq, NFData, Num, Ord, Show)

data ModelRewardProvenanceDelegate = ModelRewardProvenanceDelegate
  { _modelRewardProvenanceDelegate_stakeRegistration :: ModelTxNo,
    _modelRewardProvenanceDelegate_poolRegistration :: ModelTxNo,
    _modelRewardProvenanceDelegate_delegation :: ModelTxNo
  }
  deriving (Eq, Generic, Show)

instance NFData ModelRewardProvenanceDelegate

data ModelRewardProvenancePool = ModelRewardProvenancePool
  { _modelRewardProvenancePool_poolRegistration :: ModelTxNo
  }
  deriving (Eq, Generic, Show)

instance NFData ModelRewardProvenancePool

data ModelRewardProvenance
  = ModelRewardProvenance_Delegate ModelRewardProvenanceDelegate
  | ModelRewardProvenance_Pool ModelRewardProvenancePool
  deriving (Eq, Generic, Show)

instance NFData ModelRewardProvenance

data ModelLedger era = ModelLedger
  { _modelLedger_utxos :: (ModelUtxoMap era),
    _modelLedger_stake :: (SnapshotQueue (ModelSnapshot era)),
    _modelLedger_epoch :: EpochNo,
    _modelLedger_rewards :: GrpMap (ModelAddress (ScriptFeature era)) (Map.Map (EpochNo, ModelPoolId) (Set ModelUTxOId, ModelRewardProvenance)),
    _modelLedger_rewardUpdates :: GrpMap (ModelAddress (ScriptFeature era)) (Map.Map (EpochNo, ModelPoolId) (Set ModelUTxOId, ModelRewardProvenance)),
    _modelLedger_nextTxNo :: ModelTxNo
  }
  deriving (Eq, Show, Generic)

instance NFData (ModelLedger era)

mkModelLedger ::
  forall era.
  KnownScriptFeature (ScriptFeature era) =>
  [(ModelUTxOId, ModelAddress (ScriptFeature era), Coin)] ->
  ModelLedger era
mkModelLedger utxos =
  ModelLedger
    { _modelLedger_utxos = mkModelUtxoMap utxos,
      _modelLedger_stake = pure emptyModelSnapshot,
      _modelLedger_epoch = 0,
      _modelLedger_rewards = mempty,
      _modelLedger_rewardUpdates = mempty,
      _modelLedger_nextTxNo = 0
    }

class HasModelLedger era a | a -> era where
  modelLedger :: Lens' a (ModelLedger era)

instance HasModelLedger era (ModelLedger era) where
  modelLedger = id

modelLedger_utxos :: Lens' (ModelLedger era) (ModelUtxoMap era) -- (Map.Map ModelUTxOId (ModelTxOut era))
modelLedger_utxos a2fb s = (\b -> s {_modelLedger_utxos = b}) <$> a2fb (_modelLedger_utxos s)
{-# INLINE modelLedger_utxos #-}

modelLedger_stake :: Lens' (ModelLedger era) (SnapshotQueue (ModelSnapshot era))
modelLedger_stake a2fb s = (\b -> s {_modelLedger_stake = b}) <$> a2fb (_modelLedger_stake s)
{-# INLINE modelLedger_stake #-}

modelLedger_epoch :: Lens' (ModelLedger era) EpochNo
modelLedger_epoch a2fb s = (\b -> s {_modelLedger_epoch = b}) <$> a2fb (_modelLedger_epoch s)
{-# INLINE modelLedger_epoch #-}

modelLedger_rewards :: Lens' (ModelLedger era) (GrpMap (ModelAddress (ScriptFeature era)) ((Map.Map (EpochNo, ModelPoolId) (Set ModelUTxOId, ModelRewardProvenance))))
modelLedger_rewards a2fb s = (\b -> s {_modelLedger_rewards = b}) <$> a2fb (_modelLedger_rewards s)
{-# INLINE modelLedger_rewards #-}

modelLedger_rewardUpdates :: Lens' (ModelLedger era) (GrpMap (ModelAddress (ScriptFeature era)) ((Map.Map (EpochNo, ModelPoolId) (Set ModelUTxOId, ModelRewardProvenance))))
modelLedger_rewardUpdates a2fb s = (\b -> s {_modelLedger_rewardUpdates = b}) <$> a2fb (_modelLedger_rewardUpdates s)
{-# INLINE modelLedger_rewardUpdates #-}

modelLedger_nextTxNo :: Lens' (ModelLedger era) ModelTxNo
modelLedger_nextTxNo a2fb s = (\b -> s {_modelLedger_nextTxNo = b}) <$> a2fb (_modelLedger_nextTxNo s)

getSubAddressforUtxoMap :: ModelUtxoMap era -> ModelAddress (ScriptFeature era) -> ModelUtxoMap era
getSubAddressforUtxoMap (ModelUtxoMap utxos _) maddr = ifoldMap f utxos
  where
    f uid (_, u@(ModelTxOut maddr' _ _))
      | maddr == maddr' = (at uid .~ Just u) mempty
      | otherwise = mempty

-- applyModelDCert :: ModelDCert era -> ModelSnapshot era -> ModelSnapshot era
applyModelDCert :: ModelTxNo -> ModelDCert era -> ModelLedger era -> ModelLedger era
applyModelDCert txNo dCert = State.execState $ do
  utxosMap <- use modelLedger_utxos
  let mark = modelLedger_stake . snapshotQueue_mark
  case dCert of
    ModelRegisterStake maddr -> mark . modelSnapshot_stake . at maddr .= Just (getSubAddressforUtxoMap utxosMap maddr, txNo)
    ModelDeRegisterStake maddr -> do
      mark . modelSnapshot_stake . at maddr .= Nothing
      mark . modelSnapshot_delegations . at maddr .= Nothing
    ModelDelegate (ModelDelegation maddr poolId) -> mark . modelSnapshot_delegations . at maddr .= Just (poolId, txNo)
    ModelRegisterPool pool -> mark . modelSnapshot_pools . at (_mppId pool) .= Just (pool, txNo)
    ModelRetirePool poolId _epochNo -> mark . modelSnapshot_pools . at poolId .= Nothing

-- TODO: deal with epochNo

spendStake ::
  ModelUtxoMap era ->
  Set ModelUTxOId ->
  [(ModelUTxOId, ModelTxOut era)] ->
  ModelSnapshot era ->
  ModelSnapshot era
spendStake utxosMap ins outs = State.execState $ do
  for_ ins $ \ui -> do
    let mUiOwner = utxosMap ^. at ui
    for_ mUiOwner $ \(ModelTxOut uiOwner _ _) ->
      modelSnapshot_stake . ix uiOwner . _1 %= spendModelUTxOs (Set.singleton ui) []

  for_ outs $ \u@(_, (ModelTxOut uiOwner _ _)) -> do
    modelSnapshot_stake . ix uiOwner . _1 %= spendModelUTxOs Set.empty [u]

applyModelTx :: ModelTx era -> ModelLedger era -> ModelLedger era
applyModelTx tx = State.execState $ do
  utxosMap <- use modelLedger_utxos
  modelLedger_stake . snapshotQueue_mark %= spendStake utxosMap (_mtxInputs tx) (_mtxOutputs tx)
  -- spend inputs/add outputs
  modelLedger_utxos %= spendModelUTxOs (_mtxInputs tx) (_mtxOutputs tx)
  -- withdraw rewards
  modelLedger_rewards . _GrpMap %= (`Map.difference` (_mtxWdrl tx))

  txNo <- modelLedger_nextTxNo <+= 1

  -- apply certs
  forOf_ (modelTx_dCert . traverse) tx $ State.modify . applyModelDCert txNo

minStakeForRewards :: Coin
minStakeForRewards = Coin 200

getUtxoSetFromAddress :: ModelUtxoMap era -> Map.Map (ModelAddress (ScriptFeature era)) (Set ModelUTxOId)
getUtxoSetFromAddress (ModelUtxoMap utxos _) = Map.fromListWith Set.union $ foldr grabPairs [] $ Map.toList utxos
  where
    grabPairs (utxo, (_, (ModelTxOut addr _ _))) xs = (addr, Set.singleton utxo) : xs

getCoinUTxOsfromUTxoMap :: ModelUtxoMap era -> (Coin, Set ModelUTxOId)
getCoinUTxOsfromUTxoMap (ModelUtxoMap utxos balances) = (fold balances, Map.keysSet utxos)

getTotalDeposits :: ModelUtxoMap era -> Coin
getTotalDeposits (ModelUtxoMap _ balances) = fold balances

applyModelBlocksMade :: forall era. ModelBlocksMade -> ModelLedger era -> ModelLedger era
applyModelBlocksMade (ModelBlocksMade blocksMade) = State.execState $ do
  epochNo <- State.gets _modelLedger_epoch

  -- take a snapshot
  ModelSnapshot stakes' delegs' pools <- modelLedger_stake %%= shiftSnapshotQueue

  let stakes :: GrpMap (ModelAddress (ScriptFeature era)) (ModelUtxoMap era)
      stakes = mkGrpMap $ fmap fst stakes'
      delegs :: GrpMap ModelPoolId (Coin, Set (ModelAddress (ScriptFeature era)))
      delegs = ifoldMap (\addr (poolId, _) -> GrpMap . Map.singleton poolId $ (getTotalDeposits (view (grpMap addr) stakes), Set.singleton addr)) delegs'

      rewards :: GrpMap (ModelAddress (ScriptFeature era)) (Map.Map (EpochNo, ModelPoolId) (Set ModelUTxOId, ModelRewardProvenance))
      rewards = flip ifoldMap (Map.intersectionWith (,) blocksMade pools) $ \poolId (blockWeight, (pool, poolRegistration)) -> fold $ do
        guard (blockWeight >= 0) -- only if the pool makes *some* number of blocks
        let (dstake, deleg) = view (grpMap poolId) delegs
        guard (dstake >= _mppPledge pool) -- and the pool met its pledge
        let memberRewards, operatorRewards :: Map.Map (ModelAddress (ScriptFeature era)) (Set ModelUTxOId, ModelRewardProvenance)
            memberRewards =
              imap
                ( \i (_, a) ->
                    ( a,
                      ModelRewardProvenance_Delegate $
                        ModelRewardProvenanceDelegate
                          (maybe (error "invalid stake registration") snd $ Map.lookup i stakes')
                          poolRegistration
                          (maybe (error "invalid delegation") snd $ Map.lookup i delegs')
                    )
                )
                . Map.filter ((>= minStakeForRewards) . fst)
                $ fmap getCoinUTxOsfromUTxoMap $ -- only if they have a minimum stake amount
                  Map.restrictKeys (unGrpMap stakes) deleg -- pay the delegates
            operatorRewards =
              Map.singleton
                (_mppRAcnt pool)
                ( Set.empty, -- TODO: All of the delegates staked
                  ModelRewardProvenance_Pool $
                    ModelRewardProvenancePool poolRegistration
                )
            reward =
              (if _mppMargin pool < maxBound then memberRewards else Map.empty) -- pay delegates if margin is less than 100%
                <> (if _mppMargin pool > minBound then operatorRewards else Map.empty) -- pay the pool if the margin is more than 0%
        Just $ mkGrpMap $ fmap (Map.singleton (epochNo, poolId)) $ reward

  -- accumulate new rewards
  rewardUpdates <- modelLedger_rewardUpdates <<.= rewards

  -- distribute accumulated rewards
  modelLedger_rewards <>= rewardUpdates

  modelLedger_epoch += 1

applyModelEpoch :: ModelEpoch era -> ModelLedger era -> ModelLedger era
applyModelEpoch epoch = State.execState $ do
  forOf_ (modelEpoch_blocks . traverse . modelBlock_txSeq . traverse) epoch $ State.modify . applyModelTx
  State.modify $ applyModelBlocksMade (_modelEpoch_blocksMade epoch)

data SnapshotQueue a = SnapshotQueue
  { _snapshotQueue_mark :: a,
    _snapshotQueue_set :: a,
    _snapshotQueue_go :: a
  }
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable, Generic)

instance NFData a => NFData (SnapshotQueue a)

snapshotQueue_mark :: Lens' (SnapshotQueue a) a
snapshotQueue_mark = lens _snapshotQueue_mark (\s b -> s {_snapshotQueue_mark = b})
{-# INLINE snapshotQueue_mark #-}

snapshotQueue_set :: Lens' (SnapshotQueue a) a
snapshotQueue_set = lens _snapshotQueue_set (\s b -> s {_snapshotQueue_set = b})
{-# INLINE snapshotQueue_set #-}

snapshotQueue_go :: Lens' (SnapshotQueue a) a
snapshotQueue_go = lens _snapshotQueue_go (\s b -> s {_snapshotQueue_go = b})
{-# INLINE snapshotQueue_go #-}

shiftSnapshotQueue :: SnapshotQueue a -> (a, SnapshotQueue a)
shiftSnapshotQueue (SnapshotQueue markX setX goX) = (goX, SnapshotQueue markX markX setX)

instance Applicative SnapshotQueue where
  pure x = SnapshotQueue x x x
  SnapshotQueue markF setF goF <*> SnapshotQueue markX setX goX =
    SnapshotQueue (markF markX) (setF setX) (goF goX)

instance Monad SnapshotQueue where
  SnapshotQueue markX setX goX >>= cont =
    SnapshotQueue
      (_snapshotQueue_mark $ cont markX)
      (_snapshotQueue_set $ cont setX)
      (_snapshotQueue_go $ cont goX)

instance Semigroup a => Semigroup (SnapshotQueue a) where (<>) = liftA2 (<>)

instance Monoid a => Monoid (SnapshotQueue a) where mempty = pure mempty
