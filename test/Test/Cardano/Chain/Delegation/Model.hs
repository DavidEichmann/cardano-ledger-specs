{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE NamedFieldPuns      #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeApplications    #-}

module Test.Cardano.Chain.Delegation.Model
  ( tests
  )
where

import Cardano.Prelude

import Data.Coerce
import Data.IORef

import Hedgehog
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range

import qualified Cardano.Chain.Delegation.Validation.Scheduling as Scheduling
import qualified Control.State.Transition as STS
import qualified Control.State.Transition.Generator as STS
import Ledger.Delegation (DELEG, SDELEG)
import qualified Ledger.Delegation as Abstract

import qualified Test.Cardano.Chain.Elaboration.Delegation as E
import Test.Cardano.Crypto.Dummy (dummyProtocolMagicId)


--------------------------------------------------------------------------------
-- SDELEG Property
--------------------------------------------------------------------------------

prop_commandSDELEG :: Property
prop_commandSDELEG = withTests 25 . property $ do
  concreteRef <- liftIO $ newIORef initialConcreteState

  abstractEnv <- forAll $ STS.initEnvGen @DELEG

  actions     <- forAll $ Gen.sequential
    (Range.linear 1 20)
    initialState
    [commandSDELEG concreteRef abstractEnv]

  cleanup concreteRef >> executeSequential initialState actions
 where
  initialConcreteState = Scheduling.State mempty mempty

  cleanup :: IORef Scheduling.State -> PropertyT IO ()
  cleanup = liftIO . flip writeIORef initialConcreteState


--------------------------------------------------------------------------------
-- SDELEG State
--------------------------------------------------------------------------------

data StateSDELEG (v :: Type -> Type) = StateSDELEG
  { abstractState      :: Abstract.DSState
  , lastAbstractResult :: Either [STS.PredicateFailure SDELEG] (STS.State SDELEG)
  }

initialState :: StateSDELEG v
initialState = StateSDELEG initialAbstractState (Right initialAbstractState)
  where initialAbstractState = Abstract.DSState [] mempty


--------------------------------------------------------------------------------
-- SDELEG Signal
--------------------------------------------------------------------------------

newtype SignalSDELEG (v :: Type -> Type)
  = SignalSDELEG (STS.Signal SDELEG)
  deriving Show

instance HTraversable SignalSDELEG where
  htraverse _ s = pure (coerce s)


--------------------------------------------------------------------------------
-- SDELEG Command
--------------------------------------------------------------------------------

-- TODO: Change dcertGen to use 'MonadGen'
commandSDELEG
  :: forall m
   . MonadIO m
  => IORef Scheduling.State
  -> STS.Environment SDELEG
  -> Command Gen m StateSDELEG
commandSDELEG concreteRef abstractEnv = Command gen execute callbacks
 where
  gen :: StateSDELEG v -> Maybe (Gen (SignalSDELEG v))
  gen _ = Just $ SignalSDELEG <$> Abstract.dcertGen abstractEnv

  execute
    :: SignalSDELEG v
    -> m (Either Scheduling.Error Scheduling.State)
  execute (SignalSDELEG cert) = do
    concreteState <- liftIO $ readIORef concreteRef

    let
      result :: Either Scheduling.Error Scheduling.State
      result = Scheduling.scheduleCertificate
        (E.elaborateDSEnv abstractEnv)
        concreteState
        (E.elaborateDCertAnnotated dummyProtocolMagicId cert)

    liftIO . writeIORef concreteRef $ fromRight concreteState result

    pure result

  callbacks
    :: [ Callback
           SignalSDELEG
           (Either Scheduling.Error Scheduling.State)
           StateSDELEG
       ]
  callbacks =
    [ Update $ \StateSDELEG { abstractState } (SignalSDELEG cert) _ ->
      let
        result =
          STS.applySTS @SDELEG (STS.TRC (abstractEnv, abstractState, cert))
      in StateSDELEG (fromRight abstractState result) result
    , Ensure $ \_ StateSDELEG { lastAbstractResult } _ result -> do
      annotateShow lastAbstractResult
      annotateShow result
      isRight lastAbstractResult === isRight result
    ]


--------------------------------------------------------------------------------
-- Main Test Export
--------------------------------------------------------------------------------

tests :: IO Bool
tests = checkSequential $$discover
