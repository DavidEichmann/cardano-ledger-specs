{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -Wno-redundant-constraints #-} -- For `getIxWord`

module Cardano.Ledger.Alonzo.TxBody
  ( TxOut (TxOut, TxOutCompact, TxOutCompactDH),
    TxBody
      ( TxBody,
        inputs,
        collateral,
        outputs,
        txcerts,
        txwdrls,
        txfee,
        txvldt,
        txUpdates,
        reqSignerHashes,
        mint,
        scriptIntegrityHash,
        adHash,
        txnetworkid
      ),
    inputs',
    collateral',
    outputs',
    certs',
    wdrls',
    txfee',
    vldt',
    update',
    reqSignerHashes',
    mint',
    scriptIntegrityHash',
    adHash',
    txnetworkid',
    AlonzoBody,
    EraIndependentScriptIntegrity,
    ScriptIntegrityHash,

    -- * deprecated
    WitnessPPDataHash,

    -- MaxValueForBitLen,
    BitsToWords,
    PackedBitsLen(..),
    PackedBits(..),
    -- PackedBitsBuilder,
    getIxWord,
    getWord32,
    getWord64,
    getBool,
    getIntegral,
    setIxWord,
    setWord32,
    setWord64,
    setBool,
    setIntegral,
    -- padding,
    -- packWord32,
    -- packWord64,
    -- packBool,
    -- append
  )
where

import Cardano.Binary
  ( DecoderError (..),
    FromCBOR (..),
    ToCBOR (..),
    decodeBreakOr,
    decodeListLenOrIndef,
    encodeListLen,
  )
import Cardano.Ledger.Address (Addr)
import Cardano.Ledger.Alonzo.Data (AuxiliaryDataHash (..), DataHash)
import Cardano.Ledger.BaseTypes
  ( Network,
    StrictMaybe (..),
    isSNothing,
  )
import Cardano.Ledger.Coin (Coin)
import Cardano.Ledger.Compactible
import Cardano.Ledger.Core (PParamsDelta)
import qualified Cardano.Ledger.Core as Core
import qualified Cardano.Ledger.Crypto as CC
import Cardano.Ledger.Era (Crypto, Era)
import Cardano.Ledger.Hashes
  ( EraIndependentScriptIntegrity,
    EraIndependentTxBody,
  )
import Cardano.Ledger.Keys (KeyHash, KeyRole (..))
import Cardano.Ledger.Mary.Value (Value (..), policies, policyID)
import qualified Cardano.Ledger.Mary.Value as Mary
import Cardano.Ledger.SafeHash
  ( HashAnnotated,
    SafeHash,
    SafeToHash,
  )
import Cardano.Ledger.Shelley.CompactAddr (CompactAddr, compactAddr, decompactAddr)
import Cardano.Ledger.Shelley.Delegation.Certificates (DCert)
import Cardano.Ledger.Shelley.PParams (Update)
import Cardano.Ledger.Shelley.Scripts (ScriptHash)
import Cardano.Ledger.Shelley.TxBody (Wdrl (Wdrl), unWdrl)
import Cardano.Ledger.ShelleyMA.Timelocks (ValidityInterval (..))
import Cardano.Ledger.TxIn (TxIn (..))
import Cardano.Ledger.Val
  ( DecodeNonNegative,
    decodeMint,
    decodeNonNegative,
    encodeMint,
    isZero,
  )
import Data.Coders
import Data.Maybe (fromMaybe)
import Data.MemoBytes (Mem, MemoBytes (..), memoBytes)
import Data.Sequence.Strict (StrictSeq)
import qualified Data.Sequence.Strict as StrictSeq
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Typeable (Typeable)
import GHC.Generics (Generic)
import GHC.Records (HasField (..))
import GHC.Stack (HasCallStack)
import NoThunks.Class (InspectHeapNamed (..), NoThunks)
import Prelude hiding (lookup)
import Data.Word
import GHC.TypeLits
import Data.Kind
import Data.Proxy
import Data.Bits

-- Map is 42%
-- TxOut is 21% of the live heap
data TxOut era
  = TxOutCompact
      {-# UNPACK #-} !(CompactAddr (Crypto era))  -- data ShortByteString = SBS ByteArray# (3 Words + Payload)
        -- Hash (Core.ADDRHASH (Crypto Alonzo)) a   is 28 bytes = 3.5 words
        -- (28 * 2) + 1 = 57 bytes = 7.125 -> 8 words
        --
        -- 11 Words
      !(CompactForm (Core.Value era))             -- 3 Words (in the CompactValueAdaOnly case)

      -- 11 + 3 + 1 = 15   (adaOnly and shelley address)

      -- 1 word + 3.5 word + 1 word + 1bit + 1bit   + 1 word
      --  stake    pay cred    ada     T/M    S/P      info table
      -- 1 word + 5 words + 1 word
      -- 7 words
  | TxOutCompactDH
      {-# UNPACK #-} !(CompactAddr (Crypto era))
      !(CompactForm (Core.Value era))
      !(DataHash (Crypto era))

deriving stock instance
  ( Eq (Core.Value era),
    Compactible (Core.Value era)
  ) =>
  Eq (TxOut era)

viewCompactTxOut ::
  forall era.
  (Era era) =>
  TxOut era ->
  (Addr (Crypto era), Core.Value era, StrictMaybe (DataHash (Crypto era)))
viewCompactTxOut (TxOutCompact bs c) = (addr, val, SNothing)
  where
    addr = decompactAddr bs
    val = fromCompact c
viewCompactTxOut (TxOutCompactDH bs c dh) = (addr, val, SJust dh)
  where
    addr = decompactAddr bs
    val = fromCompact c

instance
  ( Era era,
    Show (Core.Value era),
    Show (CompactForm (Core.Value era))
  ) =>
  Show (TxOut era)
  where
  show = show . viewCompactTxOut

deriving via InspectHeapNamed "TxOut" (TxOut era) instance NoThunks (TxOut era)

pattern TxOut ::
  ( Era era,
    Compactible (Core.Value era),
    Show (Core.Value era),
    HasCallStack
  ) =>
  Addr (Crypto era) ->
  Core.Value era ->
  StrictMaybe (DataHash (Crypto era)) ->
  TxOut era
pattern TxOut addr vl dh <-
  (viewCompactTxOut -> (addr, vl, dh))
  where
    TxOut addr vl mdh =
      let v = fromMaybe (error $ "Illegal value in txout: " <> show vl) $ toCompact vl
          a = compactAddr addr
       in case mdh of
            SNothing -> TxOutCompact a v
            SJust dh -> TxOutCompactDH a v dh

{-# COMPLETE TxOut #-}

-- ======================================

type ScriptIntegrityHash crypto = SafeHash crypto EraIndependentScriptIntegrity

{-# DEPRECATED WitnessPPDataHash "Use ScriptIntegrityHash instead" #-}

type WitnessPPDataHash crypto = SafeHash crypto EraIndependentScriptIntegrity

data TxBodyRaw era = TxBodyRaw
  { _inputs :: !(Set (TxIn (Crypto era))),
    _collateral :: !(Set (TxIn (Crypto era))),
    _outputs :: !(StrictSeq (TxOut era)),
    _certs :: !(StrictSeq (DCert (Crypto era))),
    _wdrls :: !(Wdrl (Crypto era)),
    _txfee :: !Coin,
    _vldt :: !ValidityInterval,
    _update :: !(StrictMaybe (Update era)),
    _reqSignerHashes :: Set (KeyHash 'Witness (Crypto era)),
    _mint :: !(Value (Crypto era)),
    -- The spec makes it clear that the mint field is a
    -- Cardano.Ledger.Mary.Value.Value, not a Core.Value.
    -- Operations on the TxBody in the AlonzoEra depend upon this.
    _scriptIntegrityHash :: !(StrictMaybe (ScriptIntegrityHash (Crypto era))),
    _adHash :: !(StrictMaybe (AuxiliaryDataHash (Crypto era))),
    _txnetworkid :: !(StrictMaybe Network)
  }
  deriving (Generic, Typeable)

deriving instance
  ( Eq (Core.Value era),
    CC.Crypto (Crypto era),
    Compactible (Core.Value era),
    Eq (PParamsDelta era)
  ) =>
  Eq (TxBodyRaw era)

instance
  (Typeable era, NoThunks (Core.Value era), NoThunks (PParamsDelta era)) =>
  NoThunks (TxBodyRaw era)

deriving instance
  ( Era era,
    Show (Core.Value era),
    Show (PParamsDelta era)
  ) =>
  Show (TxBodyRaw era)

newtype TxBody era = TxBodyConstr (MemoBytes (TxBodyRaw era))
  deriving (ToCBOR)
  deriving newtype (SafeToHash)

deriving newtype instance
  ( Eq (Core.Value era),
    Compactible (Core.Value era),
    CC.Crypto (Crypto era),
    Eq (PParamsDelta era)
  ) =>
  Eq (TxBody era)

deriving instance
  ( Typeable era,
    NoThunks (Core.Value era),
    NoThunks (PParamsDelta era)
  ) =>
  NoThunks (TxBody era)

deriving instance
  ( Era era,
    Compactible (Core.Value era),
    Show (Core.Value era),
    Show (PParamsDelta era)
  ) =>
  Show (TxBody era)

deriving via
  (Mem (TxBodyRaw era))
  instance
    ( Era era,
      Typeable (Core.Script era),
      Typeable (Core.AuxiliaryData era),
      Compactible (Core.Value era),
      Show (Core.Value era),
      DecodeNonNegative (Core.Value era),
      FromCBOR (Annotator (Core.Script era)),
      Core.SerialisableData (PParamsDelta era)
    ) =>
    FromCBOR (Annotator (TxBody era))

-- The Set of constraints necessary to use the TxBody pattern
type AlonzoBody era =
  ( Era era,
    Compactible (Core.Value era),
    ToCBOR (Core.Script era),
    Core.SerialisableData (PParamsDelta era)
  )

pattern TxBody ::
  AlonzoBody era =>
  Set (TxIn (Crypto era)) ->
  Set (TxIn (Crypto era)) ->
  StrictSeq (TxOut era) ->
  StrictSeq (DCert (Crypto era)) ->
  Wdrl (Crypto era) ->
  Coin ->
  ValidityInterval ->
  StrictMaybe (Update era) ->
  Set (KeyHash 'Witness (Crypto era)) ->
  Value (Crypto era) ->
  StrictMaybe (ScriptIntegrityHash (Crypto era)) ->
  StrictMaybe (AuxiliaryDataHash (Crypto era)) ->
  StrictMaybe Network ->
  TxBody era
pattern TxBody
  { inputs,
    collateral,
    outputs,
    txcerts,
    txwdrls,
    txfee,
    txvldt,
    txUpdates,
    reqSignerHashes,
    mint,
    scriptIntegrityHash,
    adHash,
    txnetworkid
  } <-
  TxBodyConstr
    ( Memo
        TxBodyRaw
          { _inputs = inputs,
            _collateral = collateral,
            _outputs = outputs,
            _certs = txcerts,
            _wdrls = txwdrls,
            _txfee = txfee,
            _vldt = txvldt,
            _update = txUpdates,
            _reqSignerHashes = reqSignerHashes,
            _mint = mint,
            _scriptIntegrityHash = scriptIntegrityHash,
            _adHash = adHash,
            _txnetworkid = txnetworkid
          }
        _
      )
  where
    TxBody
      inputsX
      collateralX
      outputsX
      certsX
      wdrlsX
      txfeeX
      vldtX
      updateX
      reqSignerHashesX
      mintX
      scriptIntegrityHashX
      adHashX
      txnetworkidX =
        TxBodyConstr $
          memoBytes
            ( encodeTxBodyRaw $
                TxBodyRaw
                  inputsX
                  collateralX
                  outputsX
                  certsX
                  wdrlsX
                  txfeeX
                  vldtX
                  updateX
                  reqSignerHashesX
                  mintX
                  scriptIntegrityHashX
                  adHashX
                  txnetworkidX
            )

{-# COMPLETE TxBody #-}

instance (c ~ Crypto era) => HashAnnotated (TxBody era) EraIndependentTxBody c

-- ==============================================================================
-- We define these accessor functions manually, because if we define them using
-- the record syntax in the TxBody pattern, they inherit the (AlonzoBody era)
-- constraint as a precondition. This is unnecessary, as one can see below
-- they need not be constrained at all. This should be fixed in the GHC compiler.

inputs' :: TxBody era -> Set (TxIn (Crypto era))
collateral' :: TxBody era -> Set (TxIn (Crypto era))
outputs' :: TxBody era -> StrictSeq (TxOut era)
certs' :: TxBody era -> StrictSeq (DCert (Crypto era))
txfee' :: TxBody era -> Coin
wdrls' :: TxBody era -> Wdrl (Crypto era)
vldt' :: TxBody era -> ValidityInterval
update' :: TxBody era -> StrictMaybe (Update era)
reqSignerHashes' :: TxBody era -> Set (KeyHash 'Witness (Crypto era))
adHash' :: TxBody era -> StrictMaybe (AuxiliaryDataHash (Crypto era))
mint' :: TxBody era -> Value (Crypto era)
scriptIntegrityHash' :: TxBody era -> StrictMaybe (ScriptIntegrityHash (Crypto era))
inputs' (TxBodyConstr (Memo raw _)) = _inputs raw

txnetworkid' :: TxBody era -> StrictMaybe Network

collateral' (TxBodyConstr (Memo raw _)) = _collateral raw

outputs' (TxBodyConstr (Memo raw _)) = _outputs raw

certs' (TxBodyConstr (Memo raw _)) = _certs raw

wdrls' (TxBodyConstr (Memo raw _)) = _wdrls raw

txfee' (TxBodyConstr (Memo raw _)) = _txfee raw

vldt' (TxBodyConstr (Memo raw _)) = _vldt raw

update' (TxBodyConstr (Memo raw _)) = _update raw

reqSignerHashes' (TxBodyConstr (Memo raw _)) = _reqSignerHashes raw

adHash' (TxBodyConstr (Memo raw _)) = _adHash raw

mint' (TxBodyConstr (Memo raw _)) = _mint raw

scriptIntegrityHash' (TxBodyConstr (Memo raw _)) = _scriptIntegrityHash raw

txnetworkid' (TxBodyConstr (Memo raw _)) = _txnetworkid raw

--------------------------------------------------------------------------------
-- Serialisation
--------------------------------------------------------------------------------

instance
  ( Era era,
    Compactible (Core.Value era)
  ) =>
  ToCBOR (TxOut era)
  where
  toCBOR (TxOutCompact addr cv) =
    encodeListLen 2
      <> toCBOR addr
      <> toCBOR cv
  toCBOR (TxOutCompactDH addr cv dh) =
    encodeListLen 3
      <> toCBOR addr
      <> toCBOR cv
      <> toCBOR dh

instance
  ( Era era,
    DecodeNonNegative (Core.Value era),
    Show (Core.Value era),
    Compactible (Core.Value era)
  ) =>
  FromCBOR (TxOut era)
  where
  fromCBOR = do
    lenOrIndef <- decodeListLenOrIndef
    case lenOrIndef of
      Nothing -> do
        a <- fromCBOR
        cv <- decodeNonNegative
        decodeBreakOr >>= \case
          True -> pure $ TxOutCompact a cv
          False -> do
            dh <- fromCBOR
            decodeBreakOr >>= \case
              True -> pure $ TxOutCompactDH a cv dh
              False -> cborError $ DecoderErrorCustom "txout" "Excess terms in txout"
      Just 2 ->
        TxOutCompact
          <$> fromCBOR
          <*> decodeNonNegative
      Just 3 ->
        TxOutCompactDH
          <$> fromCBOR
          <*> decodeNonNegative
          <*> fromCBOR
      Just _ -> cborError $ DecoderErrorCustom "txout" "wrong number of terms in txout"

encodeTxBodyRaw ::
  ( Era era,
    ToCBOR (PParamsDelta era)
  ) =>
  TxBodyRaw era ->
  Encode ('Closed 'Sparse) (TxBodyRaw era)
encodeTxBodyRaw
  TxBodyRaw
    { _inputs,
      _collateral,
      _outputs,
      _certs,
      _wdrls,
      _txfee,
      _vldt = ValidityInterval bot top,
      _update,
      _reqSignerHashes,
      _mint,
      _scriptIntegrityHash,
      _adHash,
      _txnetworkid
    } =
    Keyed
      ( \i ifee o f t c w u b rsh mi sh ah ni ->
          TxBodyRaw i ifee o c w f (ValidityInterval b t) u rsh mi sh ah ni
      )
      !> Key 0 (E encodeFoldable _inputs)
      !> Key 13 (E encodeFoldable _collateral)
      !> Key 1 (E encodeFoldable _outputs)
      !> Key 2 (To _txfee)
      !> encodeKeyedStrictMaybe 3 top
      !> Omit null (Key 4 (E encodeFoldable _certs))
      !> Omit (null . unWdrl) (Key 5 (To _wdrls))
      !> encodeKeyedStrictMaybe 6 _update
      !> encodeKeyedStrictMaybe 8 bot
      !> Key 14 (E encodeFoldable _reqSignerHashes)
      !> Omit isZero (Key 9 (E encodeMint _mint))
      !> encodeKeyedStrictMaybe 11 _scriptIntegrityHash
      !> encodeKeyedStrictMaybe 7 _adHash
      !> encodeKeyedStrictMaybe 15 _txnetworkid
    where
      encodeKeyedStrictMaybe key x =
        Omit isSNothing (Key key (E (toCBOR . fromSJust) x))

      fromSJust :: StrictMaybe a -> a
      fromSJust (SJust x) = x
      fromSJust SNothing = error "SNothing in fromSJust. This should never happen, it is guarded by isSNothing"

instance
  forall era.
  ( Era era,
    Typeable (Core.Script era),
    Typeable (Core.AuxiliaryData era),
    Compactible (Core.Value era),
    Show (Core.Value era),
    DecodeNonNegative (Core.Value era),
    FromCBOR (Annotator (Core.Script era)),
    FromCBOR (PParamsDelta era),
    ToCBOR (PParamsDelta era)
  ) =>
  FromCBOR (TxBodyRaw era)
  where
  fromCBOR =
    decode $
      SparseKeyed
        "TxBodyRaw"
        initial
        bodyFields
        requiredFields
    where
      initial :: TxBodyRaw era
      initial =
        TxBodyRaw
          mempty
          mempty
          StrictSeq.empty
          StrictSeq.empty
          (Wdrl mempty)
          mempty
          (ValidityInterval SNothing SNothing)
          SNothing
          mempty
          mempty
          SNothing
          SNothing
          SNothing
      bodyFields :: (Word -> Field (TxBodyRaw era))
      bodyFields 0 =
        field
          (\x tx -> tx {_inputs = x})
          (D (decodeSet fromCBOR))
      bodyFields 13 =
        field
          (\x tx -> tx {_collateral = x})
          (D (decodeSet fromCBOR))
      bodyFields 1 =
        field
          (\x tx -> tx {_outputs = x})
          (D (decodeStrictSeq fromCBOR))
      bodyFields 2 = field (\x tx -> tx {_txfee = x}) From
      bodyFields 3 =
        field
          (\x tx -> tx {_vldt = (_vldt tx) {invalidHereafter = x}})
          (D (SJust <$> fromCBOR))
      bodyFields 4 =
        field
          (\x tx -> tx {_certs = x})
          (D (decodeStrictSeq fromCBOR))
      bodyFields 5 = field (\x tx -> tx {_wdrls = x}) From
      bodyFields 6 = field (\x tx -> tx {_update = x}) (D (SJust <$> fromCBOR))
      bodyFields 7 = field (\x tx -> tx {_adHash = x}) (D (SJust <$> fromCBOR))
      bodyFields 8 =
        field
          (\x tx -> tx {_vldt = (_vldt tx) {invalidBefore = x}})
          (D (SJust <$> fromCBOR))
      bodyFields 9 = field (\x tx -> tx {_mint = x}) (D decodeMint)
      bodyFields 11 = field (\x tx -> tx {_scriptIntegrityHash = x}) (D (SJust <$> fromCBOR))
      bodyFields 14 = field (\x tx -> tx {_reqSignerHashes = x}) (D (decodeSet fromCBOR))
      bodyFields 15 = field (\x tx -> tx {_txnetworkid = x}) (D (SJust <$> fromCBOR))
      bodyFields n = field (\_ t -> t) (Invalid n)
      requiredFields =
        [ (0, "inputs"),
          (1, "outputs"),
          (2, "fee")
        ]

instance
  ( Era era,
    Typeable (Core.Script era),
    Typeable (Core.AuxiliaryData era),
    Compactible (Core.Value era),
    Show (Core.Value era),
    DecodeNonNegative (Core.Value era),
    FromCBOR (Annotator (Core.Script era)),
    FromCBOR (PParamsDelta era),
    ToCBOR (PParamsDelta era)
  ) =>
  FromCBOR (Annotator (TxBodyRaw era))
  where
  fromCBOR = pure <$> fromCBOR

-- ====================================================
-- HasField instances to be consistent with earlier Eras

instance (Crypto era ~ c) => HasField "inputs" (TxBody era) (Set (TxIn c)) where
  getField (TxBodyConstr (Memo m _)) = _inputs m

instance HasField "outputs" (TxBody era) (StrictSeq (TxOut era)) where
  getField (TxBodyConstr (Memo m _)) = _outputs m

instance Crypto era ~ crypto => HasField "certs" (TxBody era) (StrictSeq (DCert crypto)) where
  getField (TxBodyConstr (Memo m _)) = _certs m

instance Crypto era ~ crypto => HasField "wdrls" (TxBody era) (Wdrl crypto) where
  getField (TxBodyConstr (Memo m _)) = _wdrls m

instance HasField "txfee" (TxBody era) Coin where
  getField (TxBodyConstr (Memo m _)) = _txfee m

instance HasField "update" (TxBody era) (StrictMaybe (Update era)) where
  getField (TxBodyConstr (Memo m _)) = _update m

instance
  (Crypto era ~ c) =>
  HasField "reqSignerHashes" (TxBody era) (Set (KeyHash 'Witness c))
  where
  getField (TxBodyConstr (Memo m _)) = _reqSignerHashes m

instance (Crypto era ~ c) => HasField "mint" (TxBody era) (Mary.Value c) where
  getField (TxBodyConstr (Memo m _)) = _mint m

instance (Crypto era ~ c) => HasField "collateral" (TxBody era) (Set (TxIn c)) where
  getField (TxBodyConstr (Memo m _)) = _collateral m

instance (Crypto era ~ c) => HasField "minted" (TxBody era) (Set (ScriptHash c)) where
  getField (TxBodyConstr (Memo m _)) = Set.map policyID (policies (_mint m))

instance HasField "vldt" (TxBody era) ValidityInterval where
  getField (TxBodyConstr (Memo m _)) = _vldt m

instance
  c ~ Crypto era =>
  HasField "adHash" (TxBody era) (StrictMaybe (AuxiliaryDataHash c))
  where
  getField (TxBodyConstr (Memo m _)) = _adHash m

-- | TODO deprecated
instance
  c ~ Crypto era =>
  HasField "wppHash" (TxBody era) (StrictMaybe (ScriptIntegrityHash c))
  where
  getField (TxBodyConstr (Memo m _)) = _scriptIntegrityHash m

instance
  c ~ Crypto era =>
  HasField "scriptIntegrityHash" (TxBody era) (StrictMaybe (ScriptIntegrityHash c))
  where
  getField (TxBodyConstr (Memo m _)) = _scriptIntegrityHash m

instance HasField "txnetworkid" (TxBody era) (StrictMaybe Network) where
  getField (TxBodyConstr (Memo m _)) = _txnetworkid m

instance (Crypto era ~ c) => HasField "compactAddress" (TxOut era) (CompactAddr c) where
  getField (TxOutCompact a _) = a
  getField (TxOutCompactDH a _ _) = a

instance (CC.Crypto c, Crypto era ~ c) => HasField "address" (TxOut era) (Addr c) where
  getField (TxOutCompact a _) = decompactAddr a
  getField (TxOutCompactDH a _ _) = decompactAddr a

instance (Core.Value era ~ val, Compactible val) => HasField "value" (TxOut era) val where
  getField (TxOutCompact _ v) = fromCompact v
  getField (TxOutCompactDH _ v _) = fromCompact v

instance c ~ Crypto era => HasField "datahash" (TxOut era) (StrictMaybe (DataHash c)) where
  getField (TxOutCompact _ _) = SNothing
  getField (TxOutCompactDH _ _ d) = SJust d

--
-- Bit fields
--

type a < b = (b <=? a) ~ 'False

-- | Write the integer to the given range.
setIntegral
  :: forall
     int -- Some Integral type. It's assumed that @fromIntegral@ to Word64 will project out the lowest 64 bits
     loInc -- The start index (inclusive) in the packed bits to write to.
     hiExc -- The end   index (exclusive) in the packed bits to write to.
     n
  .  ( KnownNat loInc
     , KnownNat hiExc
     , KnownNat n
     , loInc < hiExc
     , hiExc <= n
     , Integral int
     , Bits int
     , PackedBitsLen n
     )
  => Proxy loInc
  -> Proxy hiExc
  -> int
  -- ^ The bits to write. The (hiExc - loInc) lowest bits are written
  -> PackedBits n
  -> PackedBits n
setIntegral pLoInc pHiExc = unsafeSetIntegral (fromIntegral $ natVal pLoInc) (fromIntegral $ natVal pHiExc)

-- | Write the integer to the given range.
unsafeSetIntegral
  :: forall
     int -- Some Integral type. It's assumed that @fromIntegral@ to Word64 will project out the lowest 64 bits
     n
  .  ( KnownNat n
     , Integral int
     , Bits int
     , PackedBitsLen n
     )
  => Int -- ^ The start index (inclusive) in the packed bits to write to.
  -> Int -- ^ The end   index (exclusive) in the packed bits to write to.
  -> int
  -- ^ The bits to write. The (hiExc - loInc) lowest bits are written
  -> PackedBits n
  -> PackedBits n
unsafeSetIntegral loInc hiExc topBits packedbits
  | not (loInc < hiExc && hiExc < nTop) = error $
      "expected (loInc < hiExc && hiExc < n) but got (loInc, hiExc, n) = "
      ++ show (loInc, hiExc, nTop)
  | otherwise = go packedbits hiInc bitLen topBits
  where
    hiInc = hiExc - 1
    nTop = fromIntegral (natVal (Proxy @n))
    bitLen = hiExc - loInc

    go :: PackedBits n -- Current packed value
       -> Int -- Current bit index (starts from the right and moves left)
       -> Int -- number of bits remaining to be written
       -> int -- bit values remaining to be written (right aligned)
       -> PackedBits n
    go val _ 0 _ = val
    go val bitIx n bits = if bitIx `mod` 64 == 63
      -- Current bit index is at the end of a word
      then if n >= 64
        -- Write the whole word
        then go (setWord64IxUnsafe wordIx (fromIntegral bits) val) (bitIx + 64) (n - 64) (bits `shiftR` 64)
        -- Write only the right part of the bits and stop
        else let
          rightMask = (1 `shiftL` n) - 1
          leftMask = complement rightMask
          in setWord64IxUnsafe wordIx ((currWord .&. leftMask) .|. (fromIntegral bits .&. rightMask)) val
      -- Current bit index is not at the end of a word. Write to the left of
      -- the current word and continue.
      else let
        leftBitLen = bitIx `mod` 64
        rightBitLen = 64 - leftBitLen
        rightMask = (1 `shiftL` rightBitLen) - 1
        rightAlignedLeftMask = (1 `shiftL` leftBitLen) - 1
        leftMask = complement rightMask
        leftAlignedCurrWordChunk = (fromIntegral currWord .&. rightAlignedLeftMask) `shiftL` rightBitLen
        in setWord64IxUnsafe wordIx ((currWord .&. rightMask) .|. (leftAlignedCurrWordChunk .&. leftMask)) val
      where
        wordIx = bitIx `div` 64
        currWord = getWord64IxUnsafe wordIx val

-- | Get the Integer at the given bit index.
getIntegral :: forall
     int -- Some Integral type to read.
     loInc -- The start index (inclusive) in the packed bits to read.
     hiExc -- The end   index (exclusive) in the packed bits to read.
     n
  .  ( KnownNat loInc
     , KnownNat hiExc
     , KnownNat n
     , loInc < hiExc
     , hiExc <= n
     , Integral int
     , Bits int
     , PackedBitsLen n
     )
  => Proxy loInc
  -> Proxy hiExc
  -> PackedBits n
  -> int
getIntegral pLoInc pHiExc = unsafeGetIntegral (fromIntegral $ natVal pLoInc) (fromIntegral $ natVal pHiExc)

-- | Get the Integer at the given bit index.
unsafeGetIntegral :: forall
     int -- Some Integral type to read.
     n
  .  ( KnownNat n
     , Integral int
     , Bits int
     , PackedBitsLen n
     )
  => Int -- ^ The start index (inclusive) in the packed bits to read.
  -> Int -- ^ The end   index (exclusive) in the packed bits to read.
  -> PackedBits n
  -> int
unsafeGetIntegral loInc hiExc packedbits
  | not (loInc < hiExc && hiExc <= nTop) = error $
      "expected (loInc < hiExc && hiExc < n) but got (loInc, hiExc, n) = "
      ++ show (loInc, hiExc, nTop)
  | otherwise = go 0 loInc bitLen
  where
    nTop = fromIntegral (natVal (Proxy @n))
    bitLen = hiExc - loInc

    go :: int -- Accumulated bits
       -> Int -- Current bit index
       -> Int -- number of bits remaining to be read
       -> int
    go val _ 0 = val
    go val ix n = if ix `mod` 64 == 0
      -- Current bit index is at the start of a word
      then if n >= 64
        -- Consume the whole word
        then go (val `shiftL` 64 + fromIntegral currentWord) (ix + 64) (n - 64)
        -- Consume only the left part of the word and stop
        else let
          mask :: Word64
          mask = (1 `shiftL` n) - 1 -- Note shiftL will not overflow (1 <= n <= 63)
          rest = currentWord `shiftR` (64 - n) .&. mask
          in (val `shiftL` n) + fromIntegral rest
      -- Current bit index is not at the start of a word. Consume the right of
      -- the word and continue.
      else let
        consumeBitLen = 64 - (ix `mod` 64) -- 1 <= restBitLen <= 63
        consumeMask :: Word64
        consumeMask = (1 `shiftL` consumeBitLen) - 1
        in go ((val `shiftL` consumeBitLen) + (fromIntegral (currentWord .&. consumeMask)))
              (ix + consumeBitLen)
              (n - consumeBitLen)
      where
        currentWord = getWord64IxUnsafe (ix `div` 64) packedbits

-- setWord64 :: (KnownNat pos, pos <= n - 64) => Proxy pos -> Word64 -> PackedBits n ->  PackedBits n
-- setWord64 w64 = BEnd (Proxy @64) w64

-- packWord32 :: Word64 -> PackedBitsBuilder 32
-- packWord32 w32 = BEnd (Proxy @32) (fromIntegral w32 `shiftL` 32)

-- packBool :: Bool -> PackedBitsBuilder 1
-- packBool b = if b
--   then packNat (Proxy @1) (Proxy @1)
--   else packNat (Proxy @0) (Proxy @1)

--
-- Type level helpers
--

-- | Words required to store bitLen bits (ceil (bitLen / 64)).
type family BitsToWords (bitLen :: Nat) :: Nat where
  BitsToWords 0 = 0
  BitsToWords bitLen = (Div (bitLen - 1) 64) + 1 -- Note that Div rounds down

--
-- Backing datatypes using unpacked Word64s
--

class PackedBitsLen (bitLen :: Nat) where
  data PackedBits bitLen :: Type
  -- | Get the Word64 a the given index. Does not perform a bounds check.
  getWord64IxUnsafe :: Int -> PackedBits bitLen -> Word64
  -- | Set the Word64 a the given index. Does not perform a bounds check.
  setWord64IxUnsafe :: Int -> Word64 -> PackedBits bitLen -> PackedBits bitLen
  -- | All bits set to 0.
  packedBitsZero :: Proxy bitLen -> PackedBits bitLen

-- | Get the Word64 a the given word index.
getIxWord :: forall i n. (i <= ((BitsToWords n) + 1), PackedBitsLen n, KnownNat i)
  => Proxy i -> PackedBits n -> Word64
getIxWord _ = getWord64IxUnsafe (fromIntegral $ natVal (Proxy @i))

-- | Get the Word64 a the given word index.
setIxWord :: forall i n. (i <= ((BitsToWords n) + 1), PackedBitsLen n, KnownNat i)
  => Proxy i -> Word64 -> PackedBits n -> PackedBits n
setIxWord _ = setWord64IxUnsafe (fromIntegral $ natVal (Proxy @i))

-- | Get the Word64 at the given bit index.
getWord64 :: forall i n.
  ( (i + 64) <= n
  , PackedBitsLen n
  , KnownNat i
  , KnownNat n
  ) => Proxy i -> PackedBits n -> Word64
getWord64 pBitIndex = unsafeGetIntegral bitIndex (bitIndex + 64)
  where
    bitIndex = fromIntegral $ natVal pBitIndex

-- | Set the Word64 at the given bit index.
setWord64 :: forall i n.
  ( (i + 64) <= n
  , PackedBitsLen n
  , KnownNat i
  , KnownNat n
  ) => Proxy i -> Word64 -> PackedBits n -> PackedBits n
setWord64 pBitIndex = unsafeSetIntegral bitIndex (bitIndex + 64)
  where
    bitIndex = fromIntegral $ natVal pBitIndex

-- | Get the Word32 at the given bit index.
getWord32 :: forall i n.
  ( (i + 32) <= n
  , PackedBitsLen n
  , KnownNat i
  , KnownNat n
  ) => Proxy i -> PackedBits n -> Word32
getWord32 pBitIndex = unsafeGetIntegral bitIndex (bitIndex + 32)
  where
    bitIndex = fromIntegral $ natVal pBitIndex

-- | Set the Word32 at the given bit index.
setWord32 :: forall i n.
  ( (i + 32) <= n
  , PackedBitsLen n
  , KnownNat i
  , KnownNat n
  ) => Proxy i -> Word32 -> PackedBits n -> PackedBits n
setWord32 pBitIndex = unsafeSetIntegral bitIndex (bitIndex + 32)
  where
    bitIndex = fromIntegral $ natVal pBitIndex

-- | Get the Word32 at the given bit index.
getBool :: forall i n.
  ( (i + 1) <= n
  , PackedBitsLen n
  , KnownNat i
  , KnownNat n
  ) => Proxy i -> PackedBits n -> Bool
getBool pBitIndex packedbits = (1 :: Int) == (unsafeGetIntegral bitIndex (bitIndex + 1) packedbits)
  where
    bitIndex = fromIntegral $ natVal pBitIndex

-- | Set the Word32 at the given bit index.
setBool :: forall i n.
  ( (i + 1) <= n
  , PackedBitsLen n
  , KnownNat i
  , KnownNat n
  ) => Proxy i -> Bool -> PackedBits n -> PackedBits n
setBool pBitIndex b packedbits = unsafeSetIntegral bitIndex (bitIndex + 1) (if b then 1 else 0 :: Int) packedbits
  where
    bitIndex = fromIntegral $ natVal pBitIndex

boundError :: forall a b. KnownNat a => Proxy a -> Int -> b
boundError _ bound = error $ "getIxWord: index " ++ show bound ++ " is out of bounds [0-" ++ show (natVal (Proxy @a)) ++ "]"

instance PackedBitsLen 64 where
  newtype PackedBits 64 = PackedBits64 Word64
    deriving (Show)

  packedBitsZero _ = PackedBits64 0

  getWord64IxUnsafe i (PackedBits64 a) = case i of
    0 -> a
    _ -> boundError (Proxy @64) i

  setWord64IxUnsafe i v (PackedBits64 _) = case i of
    0 -> PackedBits64 v
    _ -> boundError (Proxy @64) i

instance PackedBitsLen 128 where
  data PackedBits 128 = PackedBits128
    {-# UNPACK #-} !Word64
    {-# UNPACK #-} !Word64
    deriving (Show)

  packedBitsZero _ = PackedBits128 0 0

  getWord64IxUnsafe i (PackedBits128 a b) = case i of
    0 -> a
    1 -> b
    _ -> boundError (Proxy @128) i

  setWord64IxUnsafe i v (PackedBits128 a b) = case i of
    0 -> PackedBits128 v b
    1 -> PackedBits128 a v
    _ -> boundError (Proxy @128) i

instance PackedBitsLen 192 where
  data PackedBits 192 = PackedBits192
    {-# UNPACK #-} !Word64
    {-# UNPACK #-} !Word64
    {-# UNPACK #-} !Word64
    deriving (Show)

  packedBitsZero _ = PackedBits192 0 0 0

  getWord64IxUnsafe i (PackedBits192 a b c) = case i of
    0 -> a
    1 -> b
    2 -> c
    _ -> boundError (Proxy @192) i

  setWord64IxUnsafe i v (PackedBits192 a b c) = case i of
    0 -> PackedBits192 v b c
    1 -> PackedBits192 a v c
    2 -> PackedBits192 a b v
    _ -> boundError (Proxy @192) i

instance PackedBitsLen 256 where
  data PackedBits 256 = PackedBits256
    {-# UNPACK #-} !Word64
    {-# UNPACK #-} !Word64
    {-# UNPACK #-} !Word64
    {-# UNPACK #-} !Word64
    deriving (Show)

  packedBitsZero _ = PackedBits256 0 0 0 0

  getWord64IxUnsafe i (PackedBits256 a b c d) = case i of
    0 -> a
    1 -> b
    2 -> c
    3 -> d
    _ -> boundError (Proxy @256) i

  setWord64IxUnsafe i v (PackedBits256 a b c d) = case i of
    0 -> PackedBits256 v b c d
    1 -> PackedBits256 a v c d
    2 -> PackedBits256 a b v d
    3 -> PackedBits256 a b c v
    _ -> boundError (Proxy @256) i

instance PackedBitsLen 320 where
  data PackedBits 320 = PackedBits320
    {-# UNPACK #-} !Word64
    {-# UNPACK #-} !Word64
    {-# UNPACK #-} !Word64
    {-# UNPACK #-} !Word64
    {-# UNPACK #-} !Word64
    deriving (Show)

  packedBitsZero _ = PackedBits320 0 0 0 0 0

  getWord64IxUnsafe i (PackedBits320 a b c d e) = case i of
    0 -> a
    1 -> b
    2 -> c
    3 -> d
    4 -> e
    _ -> boundError (Proxy @320) i

  setWord64IxUnsafe i v (PackedBits320 a b c d e) = case i of
    0 -> PackedBits320 v b c d e
    1 -> PackedBits320 a v c d e
    2 -> PackedBits320 a b v d e
    3 -> PackedBits320 a b c v e
    4 -> PackedBits320 a b c d v
    _ -> boundError (Proxy @320) i


