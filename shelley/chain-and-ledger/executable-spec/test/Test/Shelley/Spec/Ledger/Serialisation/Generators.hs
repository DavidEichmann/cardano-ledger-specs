{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Test.Shelley.Spec.Ledger.Serialisation.Generators () where

import Cardano.Binary
  ( ToCBOR (..),
    toCBOR,
  )
import Cardano.Crypto.DSIGN.Class (SignedDSIGN (..), rawDeserialiseSigDSIGN, sizeSigDSIGN)
import Cardano.Crypto.DSIGN.Mock (MockDSIGN, VerKeyDSIGN (..))
import Cardano.Crypto.Hash (HashAlgorithm, hashWithSerialiser)
import qualified Cardano.Crypto.Hash as Crypto
import qualified Cardano.Crypto.Hash as Monomorphic
import Cardano.Slotting.Block (BlockNo (..))
import Cardano.Slotting.Slot (EpochNo (..), SlotNo (..))
import qualified Data.ByteString.Char8 as BS
import Data.Coerce (coerce)
import Data.IP (IPv4, IPv6, toIPv4, toIPv6)
import qualified Data.Map.Strict as Map (fromList)
import Data.Maybe (fromJust)
import Data.Proxy (Proxy (..))
import Data.Ratio ((%))
import Data.Sequence.Strict (StrictSeq)
import qualified Data.Sequence.Strict as StrictSeq
import Data.Word (Word64, Word8)
import Generic.Random (genericArbitraryU)
import Numeric.Natural (Natural)
import Shelley.Spec.Ledger.Address (Addr (Addr))
import Shelley.Spec.Ledger.Address.Bootstrap
  ( ChainCode (..),
    pattern BootstrapWitness,
  )
import Shelley.Spec.Ledger.BaseTypes
  ( DnsName,
    Network,
    Nonce (..),
    Port,
    StrictMaybe,
    UnitInterval,
    Url,
    mkNonceFromNumber,
    mkUnitInterval,
    textToDns,
    textToUrl,
  )
import Shelley.Spec.Ledger.BlockChain (HashHeader (..), pattern Block)
import Shelley.Spec.Ledger.Coin (Coin (Coin))
import Shelley.Spec.Ledger.Credential (Credential (..), Ptr, StakeReference)
import Shelley.Spec.Ledger.Crypto (ADDRHASH, Crypto, HASH)
import Shelley.Spec.Ledger.Delegation.Certificates (IndividualPoolStake (..), PoolDistr (..))
import Shelley.Spec.Ledger.EpochBoundary (BlocksMade (..), Stake (..))
import Shelley.Spec.Ledger.Keys
  ( Hash,
    KeyHash (KeyHash),
    VKey (VKey),
  )
import Shelley.Spec.Ledger.LedgerState
  ( AccountState,
    EpochState (..),
    OBftSlot,
    RewardUpdate,
    WitHashes (..),
    emptyRewardUpdate,
  )
import Shelley.Spec.Ledger.MetaData (MetaDataHash (..))
import Shelley.Spec.Ledger.OCert (KESPeriod (..))
import Shelley.Spec.Ledger.PParams (PParams, ProtVer)
import Shelley.Spec.Ledger.Rewards
  ( Likelihood (..),
    LogWeight (..),
    PerformanceEstimate (..),
  )
import qualified Shelley.Spec.Ledger.STS.Chain as STS
import qualified Shelley.Spec.Ledger.STS.Ppup as STS
import qualified Shelley.Spec.Ledger.STS.Prtcl as STS (PrtclState)
import qualified Shelley.Spec.Ledger.STS.Tickn as STS
import Shelley.Spec.Ledger.Scripts
  ( MultiSig (..),
    Script (..),
    ScriptHash (ScriptHash),
  )
import Shelley.Spec.Ledger.TxData
  ( MIRPot,
    PoolMetaData (PoolMetaData),
    PoolParams (PoolParams),
    RewardAcnt (RewardAcnt),
    StakePoolRelay,
    TxId (TxId),
    TxIn (TxIn),
    TxOut (TxOut),
  )
import Test.Cardano.Prelude (genBytes)
import Test.QuickCheck
  ( Arbitrary,
    arbitrary,
    genericShrink,
    listOf,
    oneof,
    shrink,
  )
import Test.QuickCheck.Hedgehog (hedgehog)
import Test.Shelley.Spec.Ledger.Address.Bootstrap
  ( genSignature,
  )
import qualified Test.Shelley.Spec.Ledger.ConcreteCryptoTypes as Mock
import Test.Shelley.Spec.Ledger.Generator.Core
  ( KeySpace (KeySpace_),
    NatNonce (..),
    geConstants,
    geKeySpace,
    ksCoreNodes,
    mkBlock,
    mkOCert,
  )
import Test.Shelley.Spec.Ledger.Generator.Presets (genEnv)
import Test.Shelley.Spec.Ledger.Generator.Update (genPParams)
import Test.Shelley.Spec.Ledger.NonTraceProperties.Generator (genStateTx, genValidStateTx)
import Test.Tasty.QuickCheck (Gen, choose, elements)

genHash :: forall a c. Crypto c => Proxy c -> Gen (Hash c a)
genHash proxy = mkDummyHash proxy <$> arbitrary

genAddrHash :: forall a c. Crypto c => Proxy c -> Gen (Crypto.Hash (ADDRHASH c) a)
genAddrHash _ = coerce . hashWithSerialiser @(ADDRHASH c) toCBOR <$> arbitrary @Int

mkDummyHash :: forall c a. Crypto c => Proxy c -> Int -> Hash c a
mkDummyHash _ = coerce . hashWithSerialiser @(HASH c) toCBOR

{-------------------------------------------------------------------------------
  Generators

  These are generators for roundtrip tests, so the generated values are not
  necessarily valid
-------------------------------------------------------------------------------}

instance
  HashAlgorithm h =>
  Arbitrary (Mock.Block (Mock.ConcreteCrypto h))
  where
  arbitrary = do
    let KeySpace_ {ksCoreNodes} = geKeySpace (genEnv p)
    prevHash <- arbitrary :: Gen (Mock.HashHeader (Mock.ConcreteCrypto h))
    allPoolKeys <- elements (map snd ksCoreNodes)
    txs <- arbitrary
    curSlotNo <- SlotNo <$> choose (0, 10)
    curBlockNo <- BlockNo <$> choose (0, 100)
    epochNonce <- arbitrary :: Gen Nonce
    blockNonce <- NatNonce . fromIntegral <$> choose (1, 100 :: Int)
    praosLeaderValue <- arbitrary :: Gen UnitInterval
    let kesPeriod = 1
        keyRegKesPeriod = 1
        ocert = mkOCert allPoolKeys 1 (KESPeriod kesPeriod)
    return $
      mkBlock
        prevHash
        allPoolKeys
        txs
        curSlotNo
        curBlockNo
        epochNonce
        blockNonce
        praosLeaderValue
        kesPeriod
        keyRegKesPeriod
        ocert
    where
      p :: Proxy (Mock.ConcreteCrypto h)
      p = Proxy

instance HashAlgorithm h => Arbitrary (Mock.BHeader (Mock.ConcreteCrypto h)) where
  arbitrary = do
    res <- arbitrary :: Gen (Mock.Block (Mock.ConcreteCrypto h))
    return $ case res of
      Block header _ -> header
      _ -> error "SerializationProperties::BHeader - failed to deconstruct header from block"

instance Arbitrary (SignedDSIGN MockDSIGN a) where
  arbitrary =
    SignedDSIGN . fromJust . rawDeserialiseSigDSIGN
      <$> hedgehog (genBytes . fromIntegral $ sizeSigDSIGN (Proxy :: Proxy MockDSIGN))

instance HashAlgorithm h => Arbitrary (Mock.BootstrapWitness (Mock.ConcreteCrypto h)) where
  arbitrary = do
    key <- arbitrary
    sig <- genSignature
    chainCode <- ChainCode <$> arbitrary
    attributes <- arbitrary
    pure $ BootstrapWitness key sig chainCode attributes

instance Crypto c => Arbitrary (HashHeader c) where
  arbitrary = HashHeader <$> genHash (Proxy @c)

instance HashAlgorithm h => Arbitrary (Mock.Tx (Mock.ConcreteCrypto h)) where
  arbitrary = do
    (_ledgerState, _steps, _txfee, tx, _lv) <- hedgehog (genStateTx (Proxy @(Mock.ConcreteCrypto h)))
    return tx

instance Crypto c => Arbitrary (TxId c) where
  arbitrary = TxId <$> genHash (Proxy @c)

instance Crypto c => Arbitrary (TxIn c) where
  arbitrary =
    TxIn
      <$> (TxId <$> genHash (Proxy @c))
      <*> arbitrary

instance HashAlgorithm h => Arbitrary (Mock.TxOut (Mock.ConcreteCrypto h)) where
  arbitrary = TxOut <$> arbitrary <*> arbitrary

instance Arbitrary Nonce where
  arbitrary =
    oneof
      [ return NeutralNonce,
        mkNonceFromNumber <$> choose (1, 123 :: Word64)
      ]

instance Arbitrary UnitInterval where
  arbitrary = fromJust . mkUnitInterval . (% 100) <$> choose (1, 99)

instance
  (Crypto c) =>
  Arbitrary (KeyHash a c)
  where
  arbitrary = KeyHash <$> genAddrHash (Proxy @c)

instance HashAlgorithm h => Arbitrary (WitHashes (Mock.ConcreteCrypto h)) where
  arbitrary = genericArbitraryU

instance Arbitrary MIRPot where
  arbitrary = genericArbitraryU

instance Arbitrary Natural where
  arbitrary = fromInteger <$> choose (0, 1000)

instance Arbitrary STS.VotingPeriod where
  arbitrary = genericArbitraryU
  shrink = genericShrink

instance HashAlgorithm h => Arbitrary (STS.PredicateFailure (Mock.PPUP (Mock.ConcreteCrypto h))) where
  arbitrary = genericArbitraryU
  shrink = genericShrink

instance HashAlgorithm h => Arbitrary (STS.PredicateFailure (Mock.UTXO (Mock.ConcreteCrypto h))) where
  arbitrary = genericArbitraryU
  shrink = genericShrink

instance HashAlgorithm h => Arbitrary (STS.PredicateFailure (Mock.UTXOW (Mock.ConcreteCrypto h))) where
  arbitrary = genericArbitraryU
  shrink = genericShrink

instance HashAlgorithm h => Arbitrary (STS.PredicateFailure (Mock.POOL (Mock.ConcreteCrypto h))) where
  arbitrary = genericArbitraryU
  shrink = genericShrink

instance (HashAlgorithm h, forall a. Arbitrary (Crypto.Hash h a)) => Arbitrary (STS.PredicateFailure (Mock.DELPL (Mock.ConcreteCrypto h))) where
  arbitrary = genericArbitraryU
  shrink = genericShrink

instance (HashAlgorithm h, forall a. Arbitrary (Crypto.Hash h a)) => Arbitrary (STS.PredicateFailure (Mock.DELEG (Mock.ConcreteCrypto h))) where
  arbitrary = genericArbitraryU
  shrink = genericShrink

instance (HashAlgorithm h, forall a. Arbitrary (Crypto.Hash h a)) => Arbitrary (STS.PredicateFailure (Mock.DELEGS (Mock.ConcreteCrypto h))) where
  arbitrary = genericArbitraryU
  shrink = genericShrink

instance (HashAlgorithm h, forall a. Arbitrary (Crypto.Hash h a)) => Arbitrary (STS.PredicateFailure (Mock.LEDGER (Mock.ConcreteCrypto h))) where
  arbitrary = genericArbitraryU
  shrink = genericShrink

instance (HashAlgorithm h, forall a. Arbitrary (Crypto.Hash h a)) => Arbitrary (STS.PredicateFailure (Mock.LEDGERS (Mock.ConcreteCrypto h))) where
  arbitrary = genericArbitraryU
  shrink = genericShrink

instance Arbitrary Coin where
  -- Cannot be negative even though it is an 'Integer'
  arbitrary = Coin <$> choose (0, 1000)

instance Arbitrary SlotNo where
  -- Cannot be negative even though it is an 'Integer'
  arbitrary = SlotNo <$> choose (1, 100000)

instance Arbitrary EpochNo where
  -- Cannot be negative even though it is an 'Integer'
  arbitrary = EpochNo <$> choose (1, 100000)

instance HashAlgorithm h => Arbitrary (Mock.Addr (Mock.ConcreteCrypto h)) where
  arbitrary =
    oneof
      [ Addr <$> arbitrary <*> arbitrary <*> arbitrary
      -- TODO generate Byron addresses too
      -- SL.AddrBootstrap
      ]

instance HashAlgorithm h => Arbitrary (StakeReference (Mock.ConcreteCrypto h)) where
  arbitrary = genericArbitraryU
  shrink = genericShrink

instance
  ( HashAlgorithm h
  ) =>
  Arbitrary (Credential r (Mock.ConcreteCrypto h))
  where
  arbitrary =
    oneof
      [ ScriptHashObj . ScriptHash <$> genHash (Proxy @(Mock.ConcreteCrypto h)),
        KeyHashObj <$> arbitrary
      ]

instance Arbitrary Ptr where
  arbitrary = genericArbitraryU
  shrink = genericShrink

instance HashAlgorithm h => Arbitrary (RewardAcnt (Mock.ConcreteCrypto h)) where
  arbitrary = RewardAcnt <$> arbitrary <*> arbitrary

instance Arbitrary Network where
  arbitrary = genericArbitraryU
  shrink = genericShrink

instance Arbitrary (VKey kd (Mock.ConcreteCrypto h)) where
  arbitrary = VKey . VerKeyMockDSIGN <$> arbitrary

instance Arbitrary ProtVer where
  arbitrary = genericArbitraryU
  shrink = genericShrink

instance HashAlgorithm h => Arbitrary (ScriptHash (Mock.ConcreteCrypto h)) where
  arbitrary = ScriptHash <$> genHash (Proxy @(Mock.ConcreteCrypto h))

instance HashAlgorithm h => Arbitrary (MetaDataHash (Mock.ConcreteCrypto h)) where
  arbitrary = MetaDataHash <$> genHash (Proxy @(Mock.ConcreteCrypto h))

instance Arbitrary (Crypto.Hash Monomorphic.ShortHash a) where
  arbitrary = genHash (Proxy @(Mock.ConcreteCrypto Monomorphic.ShortHash))

instance Arbitrary STS.TicknState where
  arbitrary = genericArbitraryU
  shrink = genericShrink

instance HashAlgorithm h => Arbitrary (STS.PrtclState (Mock.ConcreteCrypto h)) where
  arbitrary = genericArbitraryU
  shrink = genericShrink

instance HashAlgorithm h => Arbitrary (Mock.LedgerState (Mock.ConcreteCrypto h)) where
  arbitrary = do
    (_ledgerState, _steps, _txfee, _tx, ledgerState) <- hedgehog (genValidStateTx (Proxy @(Mock.ConcreteCrypto h)))
    return ledgerState

instance HashAlgorithm h => Arbitrary (Mock.NewEpochState (Mock.ConcreteCrypto h)) where
  arbitrary = genericArbitraryU
  shrink = genericShrink

instance HashAlgorithm h => Arbitrary (BlocksMade (Mock.ConcreteCrypto h)) where
  arbitrary = BlocksMade <$> arbitrary

instance HashAlgorithm h => Arbitrary (PoolDistr (Mock.ConcreteCrypto h)) where
  arbitrary =
    PoolDistr . Map.fromList
      <$> listOf ((,) <$> arbitrary <*> genVal)
    where
      genVal = IndividualPoolStake <$> arbitrary <*> genHash (Proxy @(Mock.ConcreteCrypto h))

instance HashAlgorithm h => Arbitrary (Mock.EpochState (Mock.ConcreteCrypto h)) where
  arbitrary =
    EpochState
      <$> arbitrary
      <*> arbitrary
      <*> arbitrary
      <*> arbitrary
      <*> arbitrary
      <*> arbitrary

instance Arbitrary (RewardUpdate (Mock.ConcreteCrypto h)) where
  arbitrary = return emptyRewardUpdate

instance Arbitrary a => Arbitrary (StrictMaybe a) where
  arbitrary = genericArbitraryU
  shrink = genericShrink

instance HashAlgorithm h => Arbitrary (OBftSlot (Mock.ConcreteCrypto h)) where
  arbitrary = genericArbitraryU
  shrink = genericShrink

instance Arbitrary PParams where
  arbitrary = genPParams (geConstants (genEnv p))
    where
      p :: Proxy Mock.C
      p = Proxy

instance Arbitrary Likelihood where
  arbitrary = Likelihood <$> arbitrary

instance Arbitrary LogWeight where
  arbitrary = LogWeight <$> arbitrary

instance HashAlgorithm h => Arbitrary (Mock.NonMyopic (Mock.ConcreteCrypto h)) where
  arbitrary = genericArbitraryU
  shrink = genericShrink

instance HashAlgorithm h => Arbitrary (Mock.SnapShot (Mock.ConcreteCrypto h)) where
  arbitrary = genericArbitraryU
  shrink = genericShrink

instance HashAlgorithm h => Arbitrary (Mock.SnapShots (Mock.ConcreteCrypto h)) where
  arbitrary = genericArbitraryU
  shrink = genericShrink

instance Arbitrary PerformanceEstimate where
  arbitrary = PerformanceEstimate <$> arbitrary

instance HashAlgorithm h => Arbitrary (Mock.Stake (Mock.ConcreteCrypto h)) where
  arbitrary = Stake <$> arbitrary

instance HashAlgorithm h => Arbitrary (PoolParams (Mock.ConcreteCrypto h)) where
  arbitrary =
    PoolParams
      <$> arbitrary
      <*> genHash (Proxy @(Mock.ConcreteCrypto h))
      <*> arbitrary
      <*> arbitrary
      <*> arbitrary
      <*> arbitrary
      <*> arbitrary
      <*> arbitrary
      <*> arbitrary

instance Arbitrary PoolMetaData where
  arbitrary = (`PoolMetaData` BS.pack "bytestring") <$> arbitrary

instance Arbitrary Url where
  arbitrary = return . fromJust $ textToUrl "text"

instance Arbitrary a => Arbitrary (StrictSeq a) where
  arbitrary = StrictSeq.toStrict <$> arbitrary
  shrink = map StrictSeq.toStrict . shrink . StrictSeq.getSeq

instance Arbitrary StakePoolRelay where
  arbitrary = genericArbitraryU
  shrink = genericShrink

instance Arbitrary Port where
  arbitrary = fromIntegral @Word8 @Port <$> arbitrary

instance Arbitrary IPv4 where
  arbitrary = pure $ toIPv4 [192, 0, 2, 1]

instance Arbitrary IPv6 where
  arbitrary = pure $ toIPv6 [0x2001, 0xDB8, 0, 0, 0, 0, 0, 1]

instance Arbitrary DnsName where
  arbitrary = pure . fromJust $ textToDns "foo.example.com"

instance Arbitrary AccountState where
  arbitrary = genericArbitraryU
  shrink = genericShrink

instance
  HashAlgorithm h =>
  Arbitrary (MultiSig (Mock.ConcreteCrypto h))
  where
  arbitrary =
    oneof
      [ RequireSignature <$> arbitrary,
        RequireAllOf <$> arbitrary,
        RequireAnyOf <$> arbitrary,
        RequireMOf <$> arbitrary <*> arbitrary
      ]

instance
  HashAlgorithm h =>
  Arbitrary (Script (Mock.ConcreteCrypto h))
  where
  arbitrary = MultiSigScript <$> arbitrary
