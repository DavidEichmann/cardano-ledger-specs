{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE EmptyDataDeriving #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Cardano.Ledger.Shelley.Rules.Snap
  ( SNAP,
    PredicateFailure,
    SnapPredicateFailure,
  )
where

import Control.SetAlgebra (forwards)
import qualified Data.Map.Strict as Map
import Cardano.Ledger.Address (Addr)
import Cardano.Ledger.BaseTypes
import qualified Cardano.Ledger.Core as Core
import Cardano.Ledger.Era (Crypto)
import Cardano.Ledger.Shelley.Constraints (UsesTxOut, UsesValue)
import Cardano.Ledger.Shelley.EpochBoundary
import Cardano.Ledger.Shelley.LedgerState
  ( DPState (..),
    DState (..),
    PState (..),
    LedgerState (..),
    UTxOState (..),
    IncrementalStake(..),
    stakeDistr,
  )
import Control.State.Transition
  ( STS (..),
    TRC (..),
    TransitionRule,
    judgmentContext,
  )
import GHC.Generics (Generic)
import GHC.Records (HasField)
import NoThunks.Class (NoThunks (..))

data SNAP era

data SnapPredicateFailure era -- No predicate failures
  deriving (Show, Generic, Eq)

instance NoThunks (SnapPredicateFailure era)

instance (UsesTxOut era, UsesValue era) => STS (SNAP era) where
  type State (SNAP era) = SnapShots (Crypto era)
  type Signal (SNAP era) = ()
  type Environment (SNAP era) = LedgerState era
  type BaseM (SNAP era) = ShelleyBase
  type PredicateFailure (SNAP era) = SnapPredicateFailure era
  initialRules = [pure emptySnapShots]
  transitionRules = [snapTransition]

snapTransition ::
  ( UsesValue era,
    HasField "address" (Core.TxOut era) (Addr (Crypto era))
  ) =>
  TransitionRule (SNAP era)
snapTransition = do
  TRC (lstate, s, _) <- judgmentContext

  let LedgerState (UTxOState utxo _ fees _ (IStake sd dangle)) (DPState dstate pstate) = lstate
      stake = stakeDistr utxo dstate pstate
      -- ^ The stake distribution calculation done on the epoch boundary, which we
      -- would like to replace with an incremental one.

      rws = _rewards dstate
      ds = Cardano.Ledger.Shelley.LedgerState._delegations dstate
      ps = Cardano.Ledger.Shelley.LedgerState._pParams pstate

      -- filter the delegation mapping by the registered stake pools
      ds' = Map.filter (\pid -> pid `Map.member` ps) ds

      -- check if dangling ptrs are no-longer dangling, so we adjust by adding them back to 'sd'
      ptrs = forwards (_ptrs dstate)
      sd1 = Map.foldlWithKey' accum sd dangle
             where accum incstake p coin = 
                      case Map.lookup p ptrs of
                         Just cred -> Map.insertWith (<>) cred coin incstake
                         Nothing -> incstake
      -- add the incremental stake distribution calculation to the existing rewards                         
      sd2 = Map.unionWith (<>) sd1 rws

      -- filter the incremental stake distribution calculation to the credentials which
      -- are both registered and delegating to a registered pool
      sd3 = Stake $ Map.filterWithKey (\cred _ -> cred `Map.member` ds') sd2

      -- for debugging, this is what the epoch boundary calculation would look like
      -- if there were no rewards
      bigAggNoRewards = aggregateUtxoCoinByCredential (forwards . _ptrs $ dstate) utxo mempty

      doExplode = False

      msg = [ "\nBOOM!\n"
            , "snapshotted stake\n"
            , show (_stake stake)
            , "\nincremental stake (filtered & w/ rewards)\n"
            , show sd3
            , "\nagged in spot\n"
            , show bigAggNoRewards
            , "\nrewards\n"
            , show rws
            ]
      newMarkSnapshot =
        if doExplode && (_stake stake) /= sd3
          then (error $ mconcat msg)
          else stake
  pure $
    s
      { _pstakeMark = newMarkSnapshot,
        _pstakeSet = _pstakeMark s,
        _pstakeGo = _pstakeSet s,
        _feeSS = fees
      }
