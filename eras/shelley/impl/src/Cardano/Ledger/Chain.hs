{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Cardano.Ledger.Chain
  ( -- | Chain Checks
    ChainChecksPParams (..),
    ChainPredicateFailure (..),
    pparamsToChainChecksPParams,
    chainChecks,
    -- deprecated
    ChainChecksData,
    pparamsToChainChecksData,
  )
where

import Cardano.Ledger.BHeaderView (BHeaderView (..))
import Cardano.Ledger.BaseTypes (ProtVer (..))
import Cardano.Ledger.Era (Crypto)
import Control.Monad (unless)
import Control.Monad.Except (MonadError, throwError)
import GHC.Generics (Generic)
import GHC.Records
import NoThunks.Class (NoThunks (..))
import Numeric.Natural (Natural)

data ChainChecksPParams = ChainChecksPParams
  { ccMaxBHSize :: Natural,
    ccMaxBBSize :: Natural,
    ccProtocolVersion :: ProtVer
  }
  deriving (Show, Eq, Generic, NoThunks)

{-# DEPRECATED ChainChecksData "Use ChainChecksPParams instead" #-}

type ChainChecksData = ChainChecksPParams

pparamsToChainChecksPParams ::
  ( HasField "_maxBHSize" pp Natural,
    HasField "_maxBBSize" pp Natural,
    HasField "_protocolVersion" pp ProtVer
  ) =>
  pp ->
  ChainChecksPParams
pparamsToChainChecksPParams pp =
  ChainChecksPParams
    { ccMaxBHSize = getField @"_maxBHSize" pp,
      ccMaxBBSize = getField @"_maxBBSize" pp,
      ccProtocolVersion = getField @"_protocolVersion" pp
    }

{-# DEPRECATED pparamsToChainChecksData "Use pparamsToChainChecksPParams instead" #-}
pparamsToChainChecksData ::
  ( HasField "_maxBHSize" pp Natural,
    HasField "_maxBBSize" pp Natural,
    HasField "_protocolVersion" pp ProtVer
  ) =>
  pp ->
  ChainChecksPParams
pparamsToChainChecksData = pparamsToChainChecksPParams

data ChainPredicateFailure era
  = HeaderSizeTooLargeCHAIN
      !Natural -- Header Size
      !Natural -- Max Header Size
  | BlockSizeTooLargeCHAIN
      !Natural -- Block Size
      !Natural -- Max Block Size
  | ObsoleteNodeCHAIN
      !Natural -- protocol version used
      !Natural -- max protocol version
  deriving (Generic, Show, Eq, Ord)

instance NoThunks (ChainPredicateFailure era)

chainChecks ::
  MonadError (ChainPredicateFailure era) m =>
  Natural ->
  ChainChecksPParams ->
  BHeaderView (Crypto era) ->
  m ()
chainChecks maxpv ccd bhv = do
  unless (m <= maxpv) $ throwError (ObsoleteNodeCHAIN m maxpv)
  unless (fromIntegral (bhviewHSize bhv) <= ccMaxBHSize ccd) $
    throwError $
      HeaderSizeTooLargeCHAIN (fromIntegral $ bhviewHSize bhv) (ccMaxBHSize ccd)
  unless (bhviewBSize bhv <= ccMaxBBSize ccd) $
    throwError $
      BlockSizeTooLargeCHAIN (bhviewBSize bhv) (ccMaxBBSize ccd)
  where
    (ProtVer m _) = ccProtocolVersion ccd
