{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE NumericUnderscores #-}
{-# LANGUAGE ViewPatterns #-}
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

import qualified Control.Monad.Trans.RWS.Strict as RWS
import Cardano.Slotting.EpochInfo.API
import Cardano.Ledger.Alonzo.Scripts (ExUnits (..))
import Cardano.Ledger.Alonzo.Tx (IsValid (..))
import Cardano.Ledger.BaseTypes
import Cardano.Ledger.Coin
import GHC.Natural
import qualified Cardano.Ledger.Crypto as C
import Cardano.Ledger.Keys (KeyRole (..))
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
import Control.Monad.Reader.Class (MonadReader(..), asks)
import Control.Monad.Writer.Class (MonadWriter(..))
import Control.Monad.State.Class (MonadState)
import Data.Bifunctor (first)
import Data.Bool (bool)
import Data.Foldable (fold)
import Control.Monad.Trans.Class
import Data.Group
import Data.Kind (Type)
import qualified Data.List as List
import qualified Data.Map as Map
import qualified Data.Map.Merge.Strict as Map
import Data.Maybe (mapMaybe)
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

import Cardano.Ledger.Alonzo.PParams (PParams, PParams'(..), emptyPParams, ProtVer(..))
import Cardano.Ledger.BaseTypes

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
filterModelValueVars (ModelValue_Reward x) = ModelValue_Reward <$> filterModelCredential (reifyRequiredFeatures (Proxy @c)) x
filterModelValueVars (ModelValue_MA ys) = do
  Refl <- reifyExpectAnyOutput (reifyValueFeature (Proxy @d))
  Refl <- reifyExpectAnyOutput (reifyValueFeature (Proxy @(ValueFeature c)))

  ModelValue_MA <$> _1 filterModelScript ys

filterModelScript ::
  forall b a.
  KnownScriptFeature b =>
  ModelScript a ->
  Maybe (ModelScript b)
filterModelScript = \case
  ModelScript_Timelock t -> case reifyScriptFeature (Proxy @b) of
    ScriptFeatureTag_None -> Nothing
    ScriptFeatureTag_Simple -> Just $ ModelScript_Timelock t
    ScriptFeatureTag_PlutusV1 -> Just $ ModelScript_Timelock t
  ModelScript_PlutusV1 t -> case reifyScriptFeature (Proxy @b) of
    ScriptFeatureTag_None -> Nothing
    ScriptFeatureTag_Simple -> Nothing
    ScriptFeatureTag_PlutusV1 -> Just $ ModelScript_PlutusV1 t

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
  filterFeatures tag@(FeatureTag _ sf) (ModelTx ins outs fee dcert wdrl g cins valid rdmr wits) =
    ModelTx ins
      <$> (traverse . traverse) (filterFeatures tag) outs
      <*> (filterFeatures tag fee)
      <*> traverse (filterFeatures tag) dcert
      <*> fmap Map.fromList (for (Map.toList wdrl) $ \(k, v) -> (,) <$> filterModelCredential tag k <*> filterFeatures tag v)
      <*> ( case g of
              NoMintSupport () -> case tag of
                FeatureTag ValueFeatureTag_AdaOnly _ -> pure $ NoMintSupport ()
                FeatureTag ValueFeatureTag_AnyOutput _ -> pure (SupportsMint . ModelValue . ModelValue_Inject $ Coin 0)
              SupportsMint g' -> case tag of
                FeatureTag ValueFeatureTag_AdaOnly _ | g' == ModelValue (ModelValue_Inject $ Val.zero) -> pure $ NoMintSupport ()
                FeatureTag ValueFeatureTag_AdaOnly _ -> Nothing
                FeatureTag ValueFeatureTag_AnyOutput _ -> SupportsMint <$> filterFeatures tag g'
          )
      <*> ( let setNotEmpty :: Set x -> Maybe (Set x)
                setNotEmpty x
                  | Set.null x = Nothing
                  | otherwise = Just x
             in (fmap (mapSupportsPlutus fold) $ filterSupportsPlutus tag $ mapSupportsPlutus setNotEmpty cins)
          )
      <*> filterModelValidity sf valid
      <*> fmap Map.fromList ((traverse . _1) (filterFeatures tag) $ Map.toList rdmr)
      <*> pure wits

filterModelAddress ::
  FeatureTag b ->
  ModelAddress a ->
  Maybe (ModelAddress (ScriptFeature b))
filterModelAddress tag (ModelAddress pmt stk) =
  ModelAddress
    <$> filterModelCredential tag pmt
    <*> filterModelCredential tag stk

filterModelCredential ::
  FeatureTag b ->
  ModelCredential r a ->
  Maybe (ModelCredential r' (ScriptFeature b))
filterModelCredential (FeatureTag _ s) = \case
  ModelKeyHashObj a -> Just (ModelKeyHashObj a)
  ModelScriptHashObj a -> case s of
    ScriptFeatureTag_None -> Nothing
    ScriptFeatureTag_Simple -> Nothing
    ScriptFeatureTag_PlutusV1 -> Just (ModelScriptHashObj a)

filterModelValidity ::
  forall a b.
  ScriptFeatureTag b ->
  IfSupportsPlutus () IsValid a ->
  Maybe (IfSupportsPlutus () IsValid b)
filterModelValidity sf = hasKnownScriptFeature sf $ \case
  NoPlutusSupport () -> Just $ ifSupportsPlutus sf () (IsValid True)
  SupportsPlutus v@(IsValid True) -> Just $ ifSupportsPlutus sf () v
  SupportsPlutus v@(IsValid False) -> bitraverseSupportsPlutus id id $ ifSupportsPlutus sf Nothing (Just v)

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
  ModelValue_Reward :: ModelCredential 'Staking (ScriptFeature era) -> ModelValueVars era k
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

-- | Convenience function to create a spendable ModelTxOut
modelTxOut :: forall era. KnownScriptFeature (ScriptFeature era) => ModelAddress (ScriptFeature era) -> ModelValue (ValueFeature era) era -> ModelTxOut era
modelTxOut a v = ModelTxOut a v dh
  where
    dh = ifSupportsPlutus (Proxy :: Proxy (ScriptFeature era)) () $
      case _modelAddress_pmt a of
        ModelKeyHashObj _ -> Nothing
        ModelScriptHashObj _ -> Just $ PlutusTx.I 42

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

deriving newtype instance Show ModelUTxOId

data ModelScriptPurpose era where
  ModelScriptPurpose_Minting :: ModelScript (ScriptFeature era) -> ModelScriptPurpose era
  ModelScriptPurpose_Spending :: ModelUTxOId -> ModelScriptPurpose era
  ModelScriptPurpose_Rewarding :: ModelCredential 'Staking (ScriptFeature era) -> ModelScriptPurpose era
  ModelScriptPurpose_Certifying :: (ModelDCert era) -> ModelScriptPurpose era

deriving instance Eq (ModelScriptPurpose era)

deriving instance Ord (ModelScriptPurpose era)

deriving instance Show (ModelScriptPurpose era)

instance NFData (ModelScriptPurpose era) where
  rnf = rwhnf

instance RequiredFeatures ModelScriptPurpose where
  filterFeatures tag@(FeatureTag _ sf) = \case
    ModelScriptPurpose_Minting policy ->
      ModelScriptPurpose_Minting
        <$> hasKnownScriptFeature sf (filterModelScript policy)
    ModelScriptPurpose_Spending uid -> ModelScriptPurpose_Spending <$> pure uid
    ModelScriptPurpose_Rewarding ra -> ModelScriptPurpose_Rewarding <$> filterModelCredential tag ra
    ModelScriptPurpose_Certifying mdc -> ModelScriptPurpose_Certifying <$> filterFeatures tag mdc

data ModelTx (era :: FeatureSet) = ModelTx
  { _mtxInputs :: !(Set ModelUTxOId),
    _mtxOutputs :: ![(ModelUTxOId, ModelTxOut era)],
    _mtxFee :: !(ModelValue 'ExpectAdaOnly era),
    _mtxDCert :: ![ModelDCert era],
    _mtxWdrl :: !(Map.Map (ModelCredential 'Staking (ScriptFeature era)) (ModelValue 'ExpectAdaOnly era)),
    _mtxMint :: !(IfSupportsMint () (ModelValue (ValueFeature era) era) (ValueFeature era)),
    _mtxCollateral :: !(IfSupportsPlutus () (Set ModelUTxOId) (ScriptFeature era)),
    _mtxValidity :: !(IfSupportsPlutus () IsValid (ScriptFeature era)),
    _mtxRedeemers :: !(Map.Map (ModelScriptPurpose era) (PlutusTx.Data, ExUnits)),
    _mtxWitnessSigs :: !(Set (ModelCredential 'Witness ('TyScriptFeature 'False 'False)))
  }
  deriving (Show, Generic)

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

modelTx_wdrl :: Lens' (ModelTx era) (Map.Map (ModelCredential 'Staking (ScriptFeature era)) (ModelValue 'ExpectAdaOnly era))
modelTx_wdrl = lens _mtxWdrl (\s b -> s {_mtxWdrl = b})
{-# INLINE modelTx_wdrl #-}

modelTx_mint :: Lens' (ModelTx era) (IfSupportsMint () (ModelValue (ValueFeature era) era) (ValueFeature era))
modelTx_mint = lens _mtxMint (\s b -> s {_mtxMint = b})
{-# INLINE modelTx_mint #-}

modelTx_collateral :: Lens' (ModelTx era) (IfSupportsPlutus () (Set ModelUTxOId) (ScriptFeature era))
modelTx_collateral = lens _mtxCollateral (\s b -> s {_mtxCollateral = b})
{-# INLINE modelTx_collateral #-}

modelTx_validity :: Lens' (ModelTx era) (IfSupportsPlutus () IsValid (ScriptFeature era))
modelTx_validity = lens _mtxValidity (\s b -> s {_mtxValidity = b})
{-# INLINE modelTx_validity #-}

modelTx_redeemers :: Lens' (ModelTx era) (Map.Map (ModelScriptPurpose era) (PlutusTx.Data, ExUnits))
modelTx_redeemers = lens _mtxRedeemers (\s b -> s {_mtxRedeemers = b})
{-# INLINE modelTx_redeemers #-}

modelTx_witnessSigs :: Lens' (ModelTx era) (Set (ModelCredential 'Witness ('TyScriptFeature 'False 'False)))
modelTx_witnessSigs = lens _mtxWitnessSigs (\s b -> s {_mtxWitnessSigs = b})
{-# INLINE modelTx_witnessSigs #-}

-- | helper to produce a "blank" ModelTx with most fields set to a reasonable
-- "default"
modelTx :: forall (era :: FeatureSet). KnownRequiredFeatures era => ModelTx era
modelTx =
  ModelTx
    { _mtxInputs = Set.empty,
      _mtxOutputs = [],
      _mtxFee = ModelValue $ ModelValue_Inject $ Coin 0,
      _mtxDCert = [],
      _mtxWdrl = Map.empty,
      _mtxMint = case reifyRequiredFeatures (Proxy :: Proxy era) of
        FeatureTag v _ -> case v of
          ValueFeatureTag_AdaOnly -> NoMintSupport ()
          ValueFeatureTag_AnyOutput -> SupportsMint $ ModelValue $ ModelValue_Inject $ Coin 0,
      _mtxCollateral = mapSupportsPlutus (const Set.empty) $ reifySupportsPlutus (Proxy :: Proxy (ScriptFeature era)),
      _mtxValidity = mapSupportsPlutus (const $ IsValid True) $ reifySupportsPlutus (Proxy :: Proxy (ScriptFeature era)),
      _mtxRedeemers = Map.empty,
      _mtxWitnessSigs = Set.empty
    }

-- TODO: there's some extra degrees of freedom hidden in this function, they
-- should be exposed
-- - redeemer value/exunits
-- - how timelocks are signed (which n of m)
witnessModelTx ::
  forall (era :: FeatureSet). ModelTx era -> ModelLedger era -> ModelTx era
witnessModelTx mtx ml =
  let mkRdmr :: ModelScript (ScriptFeature era) -> ModelScriptPurpose era -> (PlutusTx.Data, ExUnits)
      mkRdmr _ _ = (PlutusTx.I 10, ExUnits 1 1)

      lookupOutput :: ModelUTxOId -> Maybe (ModelUTxOId, ModelCredential 'Payment (ScriptFeature era))
      lookupOutput ui = (,) ui <$> preview (modelLedger_utxos . at ui . _Just . modelTxOut_address @era . modelAddress_pmt) ml

      matchDCert :: ModelDCert era -> Maybe (ModelDCert era, ModelCredential 'Staking (ScriptFeature era))
      matchDCert cert = case cert of
        ModelDelegate (ModelDelegation cred _) -> Just (cert, cred)
        ModelDeRegisterStake cred -> Just (cert, cred)
        _ -> Nothing

      matchPoolCert :: ModelDCert era -> [ModelCredential 'Witness ('TyScriptFeature 'False 'False)]
      matchPoolCert = \case
        ModelRegisterPool mpp -> [coerceKeyRole' $ unModelPoolId $ _mppId mpp] <> fmap coerceKeyRole' (_mppOwners mpp)
        _ -> []

      witnessMint :: ModelValueVars era (ValueFeature era) -> (Set (ModelCredential 'Witness ('TyScriptFeature 'False 'False)), Map.Map (ModelScriptPurpose era) (PlutusTx.Data, ExUnits))
      witnessMint = \case
        ModelValue_Reward _ -> mempty
        ModelValue_MA (modelPolicy, _) -> case modelPolicy of
          ModelScript_Timelock tl -> foldMap (\wit -> (Set.singleton wit, Map.empty)) (modelScriptNeededSigs tl)
          ModelScript_PlutusV1 _s1 ->
            let sp = ModelScriptPurpose_Minting modelPolicy
             in (Set.empty, Map.singleton sp (mkRdmr modelPolicy sp))

      witnessCredential ::
        ModelScriptPurpose era ->
        ModelCredential k (ScriptFeature era) ->
        ( Set (ModelCredential 'Witness ('TyScriptFeature 'False 'False)),
          Map.Map (ModelScriptPurpose era) (PlutusTx.Data, ExUnits)
        )
      witnessCredential msp = \case
        ModelKeyHashObj k -> (Set.singleton (ModelKeyHashObj k), Map.empty)
        ModelScriptHashObj s -> (Set.empty, Map.singleton msp (mkRdmr (ModelScript_PlutusV1 s) msp))

      witnessSigs :: Set (ModelCredential 'Witness ('TyScriptFeature 'False 'False))
      redeemers :: Map.Map (ModelScriptPurpose era) (PlutusTx.Data, ExUnits)
      (witnessSigs, redeemers) =
        foldMap (uncurry witnessCredential . first ModelScriptPurpose_Spending) (mapMaybe lookupOutput $ Set.toList $ _mtxInputs mtx)
          <> foldMap (uncurry witnessCredential . first ModelScriptPurpose_Certifying) (mapMaybe matchDCert $ _mtxDCert mtx)
          <> foldMap (\c -> (Set.singleton c, Map.empty)) (matchPoolCert =<< _mtxDCert mtx)
          <> foldMap (uncurry witnessCredential . (ModelScriptPurpose_Rewarding &&& id)) (Map.keys $ _mtxWdrl mtx)
          <> fromSupportsMint mempty (foldMap witnessMint . unModelValue) (_mtxMint mtx)
          <> fromSupportsPlutus
            mempty
            (foldMap (uncurry witnessCredential . first ModelScriptPurpose_Spending) . mapMaybe lookupOutput . Set.toList)
            (_mtxCollateral mtx)
   in mtx
        { _mtxWitnessSigs = witnessSigs,
          _mtxRedeemers = redeemers
        }

data ModelBlock era = ModelBlock
  { _modelBlock_slot :: SlotNo,
    _modelBlock_txSeq :: [ModelTx era]
  }
  deriving (Show, Generic)

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

newtype ModelPoolId = ModelPoolId {unModelPoolId :: ModelCredential 'StakePool ('TyScriptFeature 'False 'False)}
  deriving (Eq, Ord, GHC.IsString, NFData)

-- always works because the wrapped credential is always KeyHashObj, and
-- consequently always like a string.
deriving newtype instance Show ModelPoolId

newtype ModelBlocksMade = ModelBlocksMade {unModelBlocksMade :: Map.Map ModelPoolId Natural}
  deriving (Generic, NFData)
  deriving Show via Quiet ModelBlocksMade
  deriving Semigroup via GrpMap ModelPoolId (Sum Natural)
  deriving Monoid via GrpMap ModelPoolId (Sum Natural)

_ModelBlocksMade :: Iso' ModelBlocksMade (Map.Map ModelPoolId Natural)
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
  deriving (Show, Generic)

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
  { _mdDelegator :: !(ModelCredential 'Staking (ScriptFeature era)),
    _mdDelegatee :: !ModelPoolId
  }
  deriving (Generic, Eq, Ord)
  deriving (Show) via Quiet (ModelDelegation era)

modelDelegation_delegator :: Lens' (ModelDelegation era) (ModelCredential 'Staking (ScriptFeature era))
modelDelegation_delegator a2fb s = (\b -> s {_mdDelegator = b}) <$> a2fb (_mdDelegator s)
{-# INLINE modelDelegation_delegator #-}

modelDelegation_delegatee :: Lens' (ModelDelegation era) ModelPoolId
modelDelegation_delegatee a2fb s = (\b -> s {_mdDelegatee = b}) <$> a2fb (_mdDelegatee s)
{-# INLINE modelDelegation_delegatee #-}

instance NFData (ModelDelegation era)

instance RequiredFeatures ModelDelegation where
  filterFeatures tag (ModelDelegation a b) =
    ModelDelegation
      <$> filterModelCredential tag a
      <*> pure b

data ModelPoolParams era = ModelPoolParams
  { _mppId :: !ModelPoolId,
    _mppVrm :: !(ModelCredential 'StakePool ('TyScriptFeature 'False 'False)),
    _mppPledge :: !Coin,
    _mppCost :: !Coin,
    _mppMargin :: !UnitInterval,
    _mppRAcnt :: !(ModelCredential 'Staking (ScriptFeature era)),
    _mppOwners :: ![ModelCredential 'Staking ('TyScriptFeature 'False 'False)]
  }
  deriving (Show, Eq, Ord, Generic)

instance NFData (ModelPoolParams era)

instance RequiredFeatures ModelPoolParams where
  filterFeatures tag (ModelPoolParams poolId poolVrf pledge cost margin rAcnt owners) =
    ModelPoolParams poolId poolVrf pledge cost margin
      <$> filterModelCredential tag rAcnt
      <*> pure owners

-- ignores genesis delegation details.
data ModelDCert era
  = ModelRegisterStake (ModelCredential 'Staking (ScriptFeature era))
  | ModelDeRegisterStake (ModelCredential 'Staking (ScriptFeature era))
  | ModelDelegate (ModelDelegation era)
  | ModelRegisterPool (ModelPoolParams era)
  | ModelRetirePool ModelPoolId EpochNo
  deriving (Show, Generic, Eq, Ord)

instance NFData (ModelDCert era)

_ModelRegisterStake :: Prism' (ModelDCert era) (ModelCredential 'Staking (ScriptFeature era))
_ModelRegisterStake = prism ModelRegisterStake $ \case
  ModelRegisterStake x -> Right x
  x -> Left x
{-# INLINE _ModelRegisterStake #-}

_ModelDeRegisterStake :: Prism' (ModelDCert era) (ModelCredential 'Staking (ScriptFeature era))
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
    ModelRegisterStake a -> ModelRegisterStake <$> filterModelCredential tag a
    ModelDeRegisterStake a -> ModelDeRegisterStake <$> filterModelCredential tag a
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

type ModelLedgerError era = ()

newtype ModelM era a = ModelM { unModelM :: RWS.RWS Globals (ModelLedgerError era) (ModelLedger era) a }
  deriving newtype (Functor, Applicative, Monad)

execModelM :: forall era. (forall m. HasModelM era (ModelLedger era) Globals m => m ()) -> Globals -> ModelLedger era -> ModelLedger era
execModelM k r s =
  let ((), s', ()) = RWS.runRWS k r s
   in s'

type HasModelM era st r m =
  ( MonadReader r m, HasGlobals r
  -- , MonadWriter (ModelLedgerError era) m
  , MonadState st m, HasModelLedger era st
  )

deriving newtype instance MonadReader Globals (ModelM era)
deriving newtype instance MonadWriter (ModelLedgerError era) (ModelM era)
deriving newtype instance MonadState (ModelLedger era) (ModelM era)

data ModelSnapshot era = ModelSnapshot
  { _modelSnapshot_stake :: GrpMap (ModelCredential 'Staking (ScriptFeature era)) Coin,
    _modelSnapshot_delegations :: Map.Map (ModelCredential 'Staking (ScriptFeature era)) ModelPoolId,
    _modelSnapshot_pools :: Map.Map ModelPoolId (ModelPoolParams era)
  }
  deriving (Eq, Generic)
  deriving (Show) via Quiet (ModelSnapshot era)

instance NFData (ModelSnapshot era)

emptyModelSnapshot :: ModelSnapshot era
emptyModelSnapshot = ModelSnapshot mempty Map.empty Map.empty

modelSnapshot_stake :: Lens' (ModelSnapshot era) (GrpMap (ModelCredential 'Staking (ScriptFeature era)) Coin)
modelSnapshot_stake a2fb s = (\b -> s {_modelSnapshot_stake = b}) <$> a2fb (_modelSnapshot_stake s)
{-# INLINE modelSnapshot_stake #-}

modelSnapshot_delegations :: Lens' (ModelSnapshot era) (Map.Map (ModelCredential 'Staking (ScriptFeature era)) ModelPoolId)
modelSnapshot_delegations a2fb s = (\b -> s {_modelSnapshot_delegations = b}) <$> a2fb (_modelSnapshot_delegations s)
{-# INLINE modelSnapshot_delegations #-}

modelSnapshot_pools :: Lens' (ModelSnapshot era) (Map.Map ModelPoolId (ModelPoolParams era))
modelSnapshot_pools a2fb s = (\b -> s {_modelSnapshot_pools = b}) <$> a2fb (_modelSnapshot_pools s)
{-# INLINE modelSnapshot_pools #-}

data ModelUTxOMap era = ModelUTxOMap
  { _modelUTxOMap_utxos :: !(Map.Map ModelUTxOId (Coin, ModelTxOut era)),
    _modelUTxOMap_stake :: !(GrpMap (ModelCredential 'Staking (ScriptFeature era)) Coin),
    _modelUTxOMap_collateralUtxos :: !(Set ModelUTxOId)
  }
  deriving (Eq, Show, Generic)

instance Semigroup (ModelUTxOMap era) where
  ModelUTxOMap utxos stake collateral <> ModelUTxOMap utxos' stake' collateral' =
    ModelUTxOMap
      (Map.unionWith (\x y -> if x == y then x else error $ unwords ["unmergable ModelUTxOMap:", show x, "/=", show y]) utxos utxos')
      (stake <> stake')
      (Set.union collateral collateral')

instance Monoid (ModelUTxOMap era) where
  mempty = ModelUTxOMap Map.empty mempty Set.empty

mkModelUTxOMap ::
  forall era.
  KnownScriptFeature (ScriptFeature era) =>
  [(ModelUTxOId, ModelAddress (ScriptFeature era), Coin)] ->
  ModelUTxOMap era
mkModelUTxOMap =
  foldMap $ \(ui, ma, val) ->
    ModelUTxOMap
      (Map.singleton ui (val, ModelTxOut ma (modelValueInject val) dh))
      (grpMapSingleton (_modelAddress_stk ma) val)
      (bool Set.empty (Set.singleton ui) $ has (modelAddress_pmt . _ModelKeyHashObj) ma)
  where
    dh = ifSupportsPlutus (Proxy :: Proxy (ScriptFeature era)) () Nothing

getModelUTxOMapTotalAda :: ModelUTxOMap era -> Coin
getModelUTxOMapTotalAda = fold . _modelUTxOMap_stake

getStake :: Map.Map ModelUTxOId (Coin, ModelTxOut era) -> GrpMap (ModelCredential 'Staking (ScriptFeature era)) Coin
getStake = foldMap (\(val, txo) -> grpMapSingleton (_modelAddress_stk $ _mtxo_address txo) val)

getModelValueCoin :: ModelValue a c -> Coin
getModelValueCoin = foldMap Val.coin . evalModelValueSimple . unModelValue

spendModelUTxOs ::
  Set ModelUTxOId ->
  [(ModelUTxOId, ModelTxOut era)] ->
  ModelUTxOMap era ->
  ModelUTxOMap era
spendModelUTxOs ins outs xs =
  let ins' = Map.restrictKeys (_modelUTxOMap_utxos xs) ins
      outs' = Map.fromList $ (fmap . fmap) (getModelValueCoin . _mtxo_value &&& id) outs
      newCollateral = foldMap (\(ui, txo) -> bool Set.empty (Set.singleton ui) $ has (modelTxOut_address . modelAddress_pmt . _ModelKeyHashObj) txo) outs
   in ModelUTxOMap
        { _modelUTxOMap_utxos = Map.withoutKeys (_modelUTxOMap_utxos xs `Map.union` outs') ins,
          _modelUTxOMap_stake = _modelUTxOMap_stake xs <> getStake outs' ~~ getStake ins',
          _modelUTxOMap_collateralUtxos =
            Set.difference (_modelUTxOMap_collateralUtxos xs) ins
              `Set.union` newCollateral
        }

instance NFData (ModelUTxOMap era)

type instance Index (ModelUTxOMap era) = ModelUTxOId

type instance IxValue (ModelUTxOMap era) = ModelTxOut era

instance Ixed (ModelUTxOMap era)

instance At (ModelUTxOMap era) where
  at :: ModelUTxOId -> Lens' (ModelUTxOMap era) (Maybe (ModelTxOut era))
  at k = \a2fb s ->
    let a = Map.lookup k $ _modelUTxOMap_utxos s
        b2t :: Maybe (ModelTxOut era) -> ModelUTxOMap era
        b2t b =
          let val = foldMap (getModelValueCoin . _mtxo_value) b
           in ModelUTxOMap
                { _modelUTxOMap_utxos = set (at k) (fmap ((,) val) b) (_modelUTxOMap_utxos s),
                  _modelUTxOMap_collateralUtxos =
                    set
                      (at k)
                      (() <$ preview (_Just . modelTxOut_address . modelAddress_pmt . _ModelKeyHashObj) b)
                      (_modelUTxOMap_collateralUtxos s),
                  _modelUTxOMap_stake =
                    _modelUTxOMap_stake s
                      <> foldMap (\(val', ui) -> grpMapSingleton (_modelAddress_stk $ _mtxo_address ui) (invert val')) a
                      <> foldMap (\ui -> grpMapSingleton (_modelAddress_stk $ _mtxo_address ui) val) b
                }
     in b2t <$> (a2fb $ fmap snd a)

data ModelAccounts = ModelAccounts
  { _modelAccounts_treasury :: !Coin
  , _modelAccounts_reserves :: !Coin
  , _modelAccounts_fees :: !Coin
  , _modelAccounts_feeSS :: !Coin
  } deriving (Eq, Show, Generic)

instance NFData ModelAccounts

-- instance Semigroup ModelAccounts where
--   ModelAccounts t r f <> ModelAccounts t' r' f' = ModelAccounts (t <> t') (r <> r') (f <> f')
--
-- instance Monoid ModelAccounts where
--   mempty = ModelAccounts mempty mempty mempty
--
-- instance Group ModelAccounts where
--   ModelAccounts t r f ~~ ModelAccounts t' r' f' = ModelAccounts (t ~~ t') (r ~~ r') (f ~~ f')
--   invert (ModelAccounts t r f) = ModelAccounts (invert t) (invert r) (invert f)
--   pow (ModelAccounts t r f) x = ModelAccounts (t `pow` x) (r `pow` x) (f `pow` x)

modelAccounts_treasury :: Lens' ModelAccounts Coin
modelAccounts_treasury a2fb s = (\b -> s {_modelAccounts_treasury = b}) <$> a2fb (_modelAccounts_treasury s)
{-# INLINE modelAccounts_treasury #-}

modelAccounts_reserves :: Lens' ModelAccounts Coin
modelAccounts_reserves a2fb s = (\b -> s {_modelAccounts_reserves = b}) <$> a2fb (_modelAccounts_reserves s)
{-# INLINE modelAccounts_reserves #-}

modelAccounts_fees :: Lens' ModelAccounts Coin
modelAccounts_fees a2fb s = (\b -> s {_modelAccounts_fees = b}) <$> a2fb (_modelAccounts_fees s)
{-# INLINE modelAccounts_fees #-}

modelAccounts_feeSS :: Lens' ModelAccounts Coin
modelAccounts_feeSS a2fb s = (\b -> s {_modelAccounts_feeSS = b}) <$> a2fb (_modelAccounts_feeSS s)
{-# INLINE modelAccounts_feeSS #-}

data ModelLedger era = ModelLedger
  { _modelLedger_utxos :: (ModelUTxOMap era),
    _modelLedger_stake :: (SnapshotQueue (ModelSnapshot era)),
    _modelLedger_epoch :: EpochNo,
    _modelLedger_rewards :: (Map.Map (ModelCredential 'Staking (ScriptFeature era)) Coin),
    _modelLedger_rewardUpdates :: !(ModelRewardUpdate era),
    _modelLedger_prevPp :: !(PParams ()),
    _modelLedger_accounts :: !ModelAccounts
  }
  deriving (Eq, Show, Generic)

instance NFData (ModelLedger era)

-- | convenient initial pparams
modelPParams :: PParams x
modelPParams = emptyPParams
  { _protocolVersion = ProtVer 5 0,
    _d = maxBound,
    _maxTxSize = 1_000_000,
    _nOpt = 10,
    _rho = case boundRational 0.02 of
      Just rho -> rho
      Nothing -> error "boundRational 0.02 out of bounds"
  }

mkModelLedger ::
  forall era.
  KnownScriptFeature (ScriptFeature era) =>
  Globals ->
  PParams () ->
  [(ModelUTxOId, ModelAddress (ScriptFeature era), Coin)] ->
  ModelLedger era
mkModelLedger globals pp utxos =
  ModelLedger
    { _modelLedger_utxos = mkModelUTxOMap utxos,
      _modelLedger_stake = pure emptyModelSnapshot,
      _modelLedger_epoch = 0,
      _modelLedger_rewards = Map.empty,
      _modelLedger_rewardUpdates = mempty,
      _modelLedger_prevPp = pp, -- emptyPParams
      _modelLedger_accounts = ModelAccounts Val.zero reserves Val.zero Val.zero
     }
  where
      reserves =
        word64ToCoin (maxLovelaceSupply globals)
          ~~ foldOf (traverse . _3) utxos

applyModelGenesisUTxOs ::
  KnownScriptFeature (ScriptFeature era) =>
  [(ModelUTxOId, ModelAddress (ScriptFeature era), Coin)] ->
  ModelLedger era ->
  ModelLedger era
applyModelGenesisUTxOs utxos =
  (modelLedger_utxos <>~ mkModelUTxOMap utxos)
  . (modelLedger_accounts . modelAccounts_reserves <>~ invert (foldOf (traverse . _3) utxos))

class HasModelLedger era a | a -> era where
  modelLedger :: Lens' a (ModelLedger era)

instance HasModelLedger era (ModelLedger era) where
  modelLedger = id

class HasGlobals a where
  getGlobals :: a -> Globals

instance HasGlobals Globals where
  getGlobals = id

modelLedger_utxos :: Lens' (ModelLedger era) (ModelUTxOMap era) -- (Map.Map ModelUTxOId (ModelTxOut era))
modelLedger_utxos a2fb s = (\b -> s {_modelLedger_utxos = b}) <$> a2fb (_modelLedger_utxos s)
{-# INLINE modelLedger_utxos #-}

modelLedger_stake :: Lens' (ModelLedger era) (SnapshotQueue (ModelSnapshot era))
modelLedger_stake a2fb s = (\b -> s {_modelLedger_stake = b}) <$> a2fb (_modelLedger_stake s)
{-# INLINE modelLedger_stake #-}

modelLedger_epoch :: Lens' (ModelLedger era) EpochNo
modelLedger_epoch a2fb s = (\b -> s {_modelLedger_epoch = b}) <$> a2fb (_modelLedger_epoch s)
{-# INLINE modelLedger_epoch #-}

modelLedger_rewards :: Lens' (ModelLedger era) (Map.Map (ModelCredential 'Staking (ScriptFeature era)) Coin)
modelLedger_rewards a2fb s = (\b -> s {_modelLedger_rewards = b}) <$> a2fb (_modelLedger_rewards s)
{-# INLINE modelLedger_rewards #-}

modelLedger_rewardUpdates :: Lens' (ModelLedger era) (ModelRewardUpdate era)
modelLedger_rewardUpdates a2fb s = (\b -> s {_modelLedger_rewardUpdates = b}) <$> a2fb (_modelLedger_rewardUpdates s)
{-# INLINE modelLedger_rewardUpdates #-}

modelLedger_accounts :: Lens' (ModelLedger era) ModelAccounts
modelLedger_accounts a2fb s = (\b -> s {_modelLedger_accounts = b}) <$> a2fb (_modelLedger_accounts s)
{-# INLINE modelLedger_accounts #-}

modelLedger_prevPp :: Lens' (ModelLedger era) (PParams ())
modelLedger_prevPp a2fb s = (\b -> s {_modelLedger_prevPp = b}) <$> a2fb (_modelLedger_prevPp s)
{-# INLINE modelLedger_prevPp #-}

-- applyModelDCert :: ModelDCert era -> ModelSnapshot era -> ModelSnapshot era
applyModelDCert :: (MonadState st m, HasModelLedger era st) => ModelDCert era -> m ()
applyModelDCert =
  let mark = modelLedger . modelLedger_stake . snapshotQueue_mark
   in \case
        ModelRegisterStake maddr -> modelLedger . modelLedger_rewards . at maddr %= (<|> Just Val.zero)
        ModelDeRegisterStake maddr -> do
          modelLedger . modelLedger_rewards . at maddr .= Nothing
          mark . modelSnapshot_delegations . at maddr .= Nothing
        ModelDelegate (ModelDelegation maddr poolId) -> mark . modelSnapshot_delegations . at maddr .= Just poolId
        ModelRegisterPool pool -> mark . modelSnapshot_pools . at (_mppId pool) .= Just pool
        -- TODO: deal with epochNo
        ModelRetirePool poolId _epochNo -> mark . modelSnapshot_pools . at poolId .= Nothing

applyModelTx :: HasModelM era st r m => ModelTx era -> m ()
applyModelTx tx = do
  -- spend inputs/add outputs
  modelLedger . modelLedger_utxos %= spendModelUTxOs (_mtxInputs tx) (_mtxOutputs tx)
  -- withdraw rewards
  modelLedger . modelLedger_rewards %= Map.merge
    Map.dropMissing
    Map.preserveMissing
    (Map.zipWithMatched $ \_ x y -> Val.zero) -- TODO: validate (== 0) (y - eval x)
    (_mtxWdrl tx)

  modelLedger . modelLedger_accounts . modelAccounts_fees <>= getModelValueCoin (_mtxFee tx)

  -- apply certs
  forOf_ (modelTx_dCert . traverse) tx applyModelDCert

minStakeForRewards :: Coin
minStakeForRewards = Coin 200

-- applyModelBlocksMade :: forall era. ModelBlocksMade -> Globals -> ModelLedger era -> ModelLedger era
applyModelBlocksMade :: forall era m st r. HasModelM era st r m => ModelBlocksMade -> m ()
applyModelBlocksMade blocksMade = do
  -- we don't actually keep the stake qty in the mark field up to date, we need
  -- to compute it's correct value at the time of snapshot.
  -- TODO: keep the stake qty up to date.
  stakeMark ::
    GrpMap (ModelCredential 'Staking (ScriptFeature era)) Coin <-
    uses (modelLedger . modelLedger_utxos) $ _modelUTxOMap_stake

  rewards <- use (modelLedger . modelLedger_rewards)

  modelLedger . modelLedger_stake . snapshotQueue_mark . modelSnapshot_stake
    .= GrpMap (Map.merge
        Map.dropMissing
        (Map.mapMissing (\_ _ -> mempty))
        (Map.zipWithMatched (\_ x _ -> x))
        (unGrpMap stakeMark)
        rewards
    )

  -- take a snapshot

  es <- use modelLedger
  rupd <- use (modelLedger . modelLedger_rewardUpdates)
  g <- asks getGlobals
  modelLedger . modelLedger_rewardUpdates .= createRUpd blocksMade es g

  modelLedger . modelLedger_stake %= snd . shiftSnapshotQueue

  applyRUpd rupd

  modelLedger . modelLedger_epoch += 1

-- applyModelEpoch :: ModelEpoch era -> Globals -> ModelLedger era -> ModelLedger era
applyModelEpoch :: HasModelM era st r m => ModelEpoch era -> m ()
applyModelEpoch epoch = do
  forOf_ (modelEpoch_blocks . traverse . modelBlock_txSeq . traverse) epoch applyModelTx
  -- State.modify $
  applyModelBlocksMade (_modelEpoch_blocksMade epoch)

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

instance NFData IsValid

data ModelRewardUpdate era = ModelRewardUpdate
  { _modelRewardUpdate_treasury :: Coin
  , _modelRewardUpdate_reserves :: Coin
  , _modelRewardUpdate_rewards :: GrpMap (ModelCredential 'Staking (ScriptFeature era)) Coin
  , _modelRewardUpdate_fees :: Coin
  } deriving (Eq, Show, Generic)

instance NFData (ModelRewardUpdate era)

instance Semigroup (ModelRewardUpdate sf) where
  ModelRewardUpdate t r sf f <> ModelRewardUpdate t' r' sf' f' = ModelRewardUpdate (t <> t') (r <> r') (sf <> sf') (f <> f')
instance Monoid (ModelRewardUpdate sf) where
  mempty = ModelRewardUpdate mempty mempty mempty mempty
instance Group (ModelRewardUpdate sf) where
  ModelRewardUpdate t r sf f ~~ ModelRewardUpdate t' r' sf' f' = ModelRewardUpdate (t ~~ t') (r ~~ r') (sf ~~ sf') (f ~~ f')
  invert (ModelRewardUpdate t r sf f) = ModelRewardUpdate (invert t) (invert r) (invert sf) (invert f)
  pow (ModelRewardUpdate t r sf f) x = ModelRewardUpdate (t `pow` x) (r `pow` x) (sf `pow` x) (f `pow` x)

-- | Reward Update Application
-- [SL-D5] Figure 52
applyRUpd :: (MonadState st m, HasModelLedger era st) => ModelRewardUpdate era -> m ()
applyRUpd (ModelRewardUpdate deltaT deltaR (GrpMap rs) deltaF) = do
  rewards <- use $ modelLedger . modelLedger_rewards
  let regRU = Map.intersection rs rewards
      unregRU = Map.difference rs rewards
      unregRU' = fold unregRU
  modelLedger . modelLedger_accounts . modelAccounts_treasury <>= deltaT <> unregRU'
  modelLedger . modelLedger_accounts . modelAccounts_reserves <>= deltaR
  modelLedger . modelLedger_rewards %= Map.unionWith (<>) regRU
  modelLedger . modelLedger_accounts . modelAccounts_fees <>= deltaF

modelTotalAda :: ModelLedger era -> Coin
modelTotalAda = foldOf $
  modelLedger_accounts .
    (modelAccounts_treasury
     <> modelAccounts_reserves
     <> modelAccounts_fees)
  <> modelLedger_rewards . folded
  <> modelLedger_utxos . to getModelUTxOMapTotalAda
  <> to getModelLedgerDeposits

getModelLedgerDeposits :: ModelLedger era -> Coin
getModelLedgerDeposits l
  = _keyDeposit (_modelLedger_prevPp l) `pow` lengthOf modelLedger_rewards l
  <> _poolDeposit (_modelLedger_prevPp l) `pow` lengthOf (modelLedger_stake . snapshotQueue_mark . modelSnapshot_pools) l

-- | calculation to create a reward update
-- [SL-D5] Figure 51
createRUpd :: ModelBlocksMade -> ModelLedger era -> Globals -> ModelRewardUpdate era
createRUpd
    b
    myModelLedger@(ModelLedger
      { _modelLedger_prevPp = prevPp@(PParams
        { _d = unboundRational -> d
        , _tau = unboundRational -> tau
        , _rho = unboundRational -> rho
        })
      , _modelLedger_epoch = currentEpoch
      , _modelLedger_stake = SnapshotQueue
        { _snapshotQueue_go = ModelSnapshot
          { _modelSnapshot_stake = GrpMap stake
          , _modelSnapshot_delegations = delegs
          , _modelSnapshot_pools = poolSS
          }
        }
      , _modelLedger_accounts = ModelAccounts
        { _modelAccounts_reserves = reserves
        , _modelAccounts_fees = feeSS
        }
      , _modelLedger_rewards = rewards
      })
    globals
    = validRU $ ModelRewardUpdate
      { _modelRewardUpdate_treasury = deltaT1
      , _modelRewardUpdate_reserves = deltaR2 ~~ deltaR1
      , _modelRewardUpdate_rewards = mkGrpMap rs
      , _modelRewardUpdate_fees = invert feeSS
      }
  where
    validRU ru@(ModelRewardUpdate a b c d) = runIdentity $ do
      when (a <> b <> fold c <> d /= mempty) $ error ("createRUpd unbalanced:" <> show ru)
      when (a < mempty) $ error ("createRUpd treasury<0 " <> show ru)
      when (b > mempty) $ error ("createRUpd reserves>0 " <> show ru <> "/" <> show deltaR2 <> "-" <> show deltaR1)
      when (d > mempty) $ error ("createRUpd fees>0 " <> show ru)
      pure ru
    slotsPerEpoch = toRational $ runIdentity $ epochInfoSize (epochInfo globals) currentEpoch
    total = Coin $ toInteger $ maxLovelaceSupply globals
    deltaR1 = rationalToCoin (min 1 eta * rho * coinToRational reserves)
    activeSlotCoeff' = unboundRational $ activeSlotVal $ activeSlotCoeff globals
    eta
      | d >= 0.8 = 1
      | otherwise = blocksMade / toRational (floor $ (1 - d) * slotsPerEpoch * activeSlotCoeff' :: Integer)
    rewardPot = feeSS <> deltaR1
    deltaT1 = rationalToCoin (tau * coinToRational rewardPot)
    r = rewardPot ~~ deltaT1
    circulation = total ~~ reserves
    rs = rewardModel prevPp b r (Map.keysSet rewards) poolSS stake delegs circulation
    deltaR2 = r ~~ fold rs
    blocksMade = toRational $ sum (unModelBlocksMade b)

rationalToCoin :: Rational -> Coin
rationalToCoin = Coin . floor

-- |
-- [SL-D5] Figure 46
-- [SL-D1] 5.5.2 f(s, σ)
maxPoolModel :: PParams x -> Coin -> UnitInterval -> UnitInterval -> Coin
maxPoolModel
    PParams {_a0 = (unboundRational -> a0), _nOpt = (toRational -> nOpt)}
    (coinToRational -> r)
    (unboundRational -> sigma)
    (unboundRational -> pr) =
  rationalToCoin ( r / (1 + a0) * (sigma' + p' * a0 * (sigma' - p' * (z0 - sigma') / z0 ) / z0 ) )
  where
    z0 = 1 / nOpt
    sigma' = min sigma z0
    p' = min pr z0

-- |
-- [SL-D5] Figure 46
-- [SL-D1] 5.5.2 (p-hat)
mkApparentPerformance ::
  UnitInterval ->
  UnitInterval ->
  Natural ->
  Natural ->
  Rational
mkApparentPerformance (unboundRational -> d) (unboundRational -> sigma) (toRational -> n) (toRational -> nbar)
  | d < 0.8 = beta / sigma
  | otherwise = 1
  where
    beta = n / max 1 nbar

-- |
-- [SL-D5] Figure 47
-- [SL-D1] 5.5.3
r_operator :: Coin -> ModelPoolParams era -> UnitInterval -> PositiveUnitInterval -> Coin
r_operator f_hat (ModelPoolParams {_mppCost = c, _mppMargin = (unboundRational -> m)}) (unboundRational -> s) (unboundRational -> sigma)
  | f_hat <= c = f_hat
  | otherwise = c <> rationalToCoin ((coinToRational $ f_hat ~~ c) * (m + (1 - m) * s / sigma))

-- |
-- [SL-D5] Figure 47
-- [SL-D1] 5.5.3
r_member :: Coin -> ModelPoolParams era -> UnitInterval -> PositiveUnitInterval -> Coin
r_member f_hat (ModelPoolParams {_mppCost = c, _mppMargin = (unboundRational -> m)}) (unboundRational -> t) (unboundRational -> sigma)
  | f_hat <= c = Val.zero
  | otherwise = rationalToCoin ((coinToRational $ f_hat ~~ c) * (1 - m) * t / sigma)

unsafeFromRational :: BoundedRational r => String -> Rational -> r
unsafeFromRational clue x = maybe (error $ "unsafeFromRational " <> clue <> " out of bounds:" <> show x) id $ boundRational x

rewardOnePoolModel ::
  PParams x ->
  Coin ->
  Natural ->
  Natural ->
  ModelPoolParams era ->
  Map.Map (ModelCredential 'Staking (ScriptFeature era)) Coin ->
  Rational ->
  UnitInterval ->
  Coin ->
  Set (ModelCredential 'Staking (ScriptFeature era)) ->
  Map.Map (ModelCredential 'Staking (ScriptFeature era)) Coin
rewardOnePoolModel
    pp
    r
    n
    nbar
    pool@(ModelPoolParams {_mppPledge = (coinToRational -> pledge)})
    stake
    sigma
    sigma_a
    (coinToRational -> tot)
    addrs_rew
    = rewards
  where
    ostake = coinToRational $ fold stake
    p_r = unsafeFromRational "rewardOnePoolModel::p_r" $ pledge / tot
    maxP
      | pledge <= ostake = maxPoolModel pp r (unsafeFromRational "rewardOnePoolModel::sigma" sigma) p_r
      | otherwise = Val.zero
    appPerf = mkApparentPerformance (_d pp) sigma_a n nbar
    poolR = rationalToCoin (appPerf * coinToRational maxP)
    mRewards = Map.fromList
      [ (hk, r_member poolR pool (unsafeFromRational "rewardOnePoolModel::c/tot" $ c / tot) (unsafeFromRational "rewardOnePoolModel::sigma" sigma))
      | (hk, (coinToRational -> c)) <- Map.toList stake
      , not (elem hk $ fmap liftModelCredential $ _mppOwners pool)
      ]
    iReward = r_operator poolR pool (unsafeFromRational "rewardOnePoolModel::ostake/tot" $ ostake / tot) (unsafeFromRational "rewardOnePoolModel::sigma" sigma)
    potentialRewards = Map.unionWith (<>) mRewards (Map.singleton (_mppRAcnt pool) iReward)
    rewards = Map.restrictKeys potentialRewards addrs_rew

-- |
-- [SL-D5] Figure 34
poolStakeModel ::
  ModelPoolId ->
  Map.Map (ModelCredential 'Staking sf) ModelPoolId ->
  Map.Map (ModelCredential 'Staking sf) Coin ->
  Map.Map (ModelCredential 'Staking sf) Coin
poolStakeModel hk delegs stake = Map.intersection stake (Map.filter (== hk) delegs)

rewardModel ::
  forall era x.
  PParams x ->
  ModelBlocksMade ->
  Coin ->
  Set (ModelCredential 'Staking (ScriptFeature era)) ->
  Map.Map ModelPoolId (ModelPoolParams era) ->
  Map.Map (ModelCredential 'Staking (ScriptFeature era)) Coin ->
  Map.Map (ModelCredential 'Staking (ScriptFeature era)) ModelPoolId ->
  Coin ->
  Map.Map (ModelCredential 'Staking (ScriptFeature era)) Coin
rewardModel
    pp
    (ModelBlocksMade blocks)
    r
    addrs_rew
    poolParams
    stake
    delegs
    total = rewards
  where
    total_a = coinToRational $ fold stake
    nbar = sum blocks
    pdata = Map.intersectionWithKey
      (\hk p n -> (p, n, poolStakeModel hk delegs stake))
      poolParams
      blocks
    results = Map.fromList
      [ (hk, rewardOnePoolModel
              pp
              r
              n
              nbar
              p
              s
              (sbar / coinToRational total)
              (unsafeFromRational "rewardModel::sbar/total_a" $ sbar / total_a)
              total
              addrs_rew)
      | (hk, (p, n, s)) <- Map.toList pdata
      , let sbar = coinToRational (fold s)
      ]
    rewards = Map.unionsWith (<>) results
