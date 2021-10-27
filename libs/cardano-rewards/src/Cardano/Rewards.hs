{-# LANGUAGE DerivingVia #-}

module Cardano.Rewards where

import Data.Foldable (fold)
import qualified Data.Map as Map
import Data.Map (Map)
import Data.Monoid (Sum (..))
import Data.Maybe (fromMaybe)
import Data.Ratio (Rational, (%))
import qualified Data.Set as Set
import Data.Set (Set)

newtype Coin = Coin Integer
  deriving (Show, Eq, Ord)
  deriving (Semigroup, Monoid, Num) via Sum Integer

newtype BlockCount = BlockCount { unBlockCount :: Integer }
  deriving (Show, Eq, Ord)
  deriving (Semigroup, Monoid, Num) via Sum Integer

coinFloor :: Rational -> Coin
coinFloor = Coin . floor

coinToQ :: Coin -> Rational
coinToQ (Coin c) = fromIntegral c

coinRatio :: Coin -> Coin -> Rational
coinRatio (Coin x) (Coin y) = x % y

newtype StakeCredential c = StakeCredential c
  deriving (Show, Eq, Ord)

newtype PoolID p = PoolID p
  deriving (Show, Eq, Ord)

data PoolParameters c =
  PoolParameters
    { cost   :: Coin,
      margin :: Rational,
      pledge :: Coin,
      owners :: Set (StakeCredential c),
      poolSC :: StakeCredential c
    } deriving (Show)

data ProtocolParameters =
  ProtocolParameters
    { asc  :: Rational
    , d    :: Rational
    , κ :: Integer
    , ρ    :: Rational
    , τ  :: Rational
    }

data PoolRewardInfo c =
  PoolRewardInfo
    { pooledStake :: StakeDistribution c
    , poolRelativeStake :: Rational
    , ownerStake :: Coin
    , poolPot :: Coin
    , poolPs :: PoolParameters c
    } deriving (Show)

type Rewards c           = Map (StakeCredential c) Coin
type StakeDistribution c = Map (StakeCredential c) Coin
type Delgations p c      = Map (StakeCredential c) (PoolID p)
type Pools p c           = Map (PoolID p) (PoolParameters c)
type BlocksMade p        = Map (PoolID p) BlockCount

maxSupply :: Coin
maxSupply = 45000000

slotsPerEpoch :: Integer
slotsPerEpoch = 100

maxPool ::
  ProtocolParameters ->
  Coin ->
  Rational ->
  Rational ->
  Coin
maxPool pp r sigma pR = coinFloor $ factor1 * factor2
  where
    z0 = 1 % κ pp
    sigma' = min sigma z0
    p' = min pR z0
    factor1 :: Rational
    factor1 = coinToQ r / (1 + asc pp)
    factor2 = sigma' + p' * asc pp * factor3
    factor3 = (sigma' - p' * factor4) / z0
    factor4 = (z0 - sigma') / z0

mkApparentPerformance ::
  ProtocolParameters ->
  Rational ->
  BlockCount ->
  BlockCount ->
  Rational
mkApparentPerformance pp sigma (BlockCount blocksN) (BlockCount blocksTotal)
  | sigma == 0 = 0
  | d pp < 0.8 = beta / sigma
  | otherwise = 1
  where
    beta = blocksN % max 1 blocksTotal


maxP ::
  ProtocolParameters ->
  PoolParameters c ->
  Coin ->
  Coin ->
  Rational ->
  Coin ->
  Coin
maxP pp pool r totalStake sigma ownerStake =
  if pledge pool <= ownerStake
    then maxPool pp r sigma pledgeRatio
    else 0
  where
    pledgeRatio = coinRatio (pledge pool) totalStake

poolR ::
  ProtocolParameters ->
  PoolParameters c ->
  Rational ->
  BlockCount ->
  BlockCount ->
  Coin ->
  Coin ->
  Rational ->
  Coin ->
  Coin
poolR pp pool sigmaA blocksN blocksTotal totalStake r sigma ownerStake =
  coinFloor (appPerf * coinToQ mp)
  where
    appPerf = mkApparentPerformance pp sigmaA blocksN blocksTotal
    mp = maxP pp pool r totalStake sigma ownerStake


-- | Calculate pool leader reward
leaderRew ::
  Coin ->
  PoolParameters c ->
  Rational ->
  Rational ->
  Coin
leaderRew f pool s sigma
  | f <= c = f
  | otherwise =
    c <> coinFloor (coinToQ (f - c) * (m + (1 - m) * s / sigma))
  where
    c = cost pool
    m = margin pool

-- | Calculate pool member reward
memberRew ::
  Coin ->
  PoolParameters c ->
  Rational ->
  Rational ->
  Coin
memberRew f pool t sigma
  | f <= c = mempty
  | otherwise =
    coinFloor $ coinToQ (f - c) * (1 - m) * t / sigma
  where
    c = cost pool
    m = margin pool

rewardOnePool ::
  Ord c =>
  Coin ->
  PoolParameters c ->
  PoolRewardInfo c ->
  Rewards c
rewardOnePool
  totalStake
  pool
  (PoolRewardInfo stake sigma ownerStake poolPot poolRI) = rewards
    where
      f c = memberRew poolPot pool (coinRatio c totalStake) sigma
      mRewards = Map.map f (Map.filterWithKey notPoolOwner stake)
      notPoolOwner cred _ = cred `Set.notMember` owners poolRI
      lReward = leaderRew poolPot pool (coinRatio ownerStake totalStake) sigma
      rewards = Map.insertWith (<>) (poolSC pool) lReward mRewards

poolRewardInfo ::
  (Eq p, Ord p, Ord c, Show c) =>
  ProtocolParameters ->
  BlocksMade p ->
  BlockCount ->
  StakeDistribution c ->
  Delgations p c ->
  Coin ->
  Coin ->
  Coin ->
  PoolID p ->
  PoolParameters c ->
  PoolRewardInfo c
poolRewardInfo pp blocks blocksTotal sd delegations totalStake total_a r pid pool =
  PoolRewardInfo { pooledStake = pstake
                 , poolRelativeStake = sigma'
                 , ownerStake = ostk
                 , poolPot = poolR'
                 , poolPs = pool
                 }
  where
    pstake = poolStake pid delegations sd
    pstakeTot = sum pstake
    ostk = Set.foldl' (\c o -> c + Map.findWithDefault 0 o pstake) 0 (owners pool)
    blocksN = Map.findWithDefault 0 pid blocks
    sigma' = coinRatio pstakeTot totalStake
    sigmaA' = coinRatio pstakeTot total_a
    poolR' = poolR pp pool sigmaA' blocksN blocksTotal totalStake r sigma' ostk

-- | Get stake of one pool
poolStake ::
  (Eq p, Ord c) =>
  PoolID p ->
  Delgations p c ->
  StakeDistribution c ->
  StakeDistribution c
poolStake poolID delegations =
  Map.filterWithKey f
  where
    f cred _ =
      case Map.lookup cred delegations of
        Nothing -> False
        Just p -> p == poolID

rewards ::
  (Ord p, Ord c, Show c) =>
  ProtocolParameters ->
  Pools p c ->
  BlocksMade p ->
  Delgations p c ->
  StakeDistribution c ->
  Coin ->
  Coin ->
  Rewards c
rewards pp pools blocks delegations sd fees reserves =
  Map.foldlWithKey f mempty pools
  where
    f acc pid pool =
      Map.unionWith (<>) acc $
        rewardOnePool
          totalStake
          pool
          (poolRewardInfo pp blocks blocksTotal sd delegations totalStake totA _R pid pool)
    (_R, totalStake, blocksTotal) = getRewardParameters pp blocks fees reserves
    totA = sum sd

-- REWRITE --

getRewardParameters ::
  ProtocolParameters ->
  BlocksMade p ->
  Coin ->
  Coin ->
  (Coin, Coin, BlockCount)
getRewardParameters pp blocks fees reserves =
  (_R, totalStake, blocksTotal)
  where
    blocksTotal = sum blocks
    expectedBlocks = floor $ (1 - d pp) * asc pp * fromIntegral slotsPerEpoch
    η
      | d pp >= 0.8 = 1
      | otherwise = unBlockCount blocksTotal % expectedBlocks
    δr = coinFloor $ min 1 η * ρ pp * coinToQ reserves
    rewardPot = fees + δr
    δt = coinFloor $ τ pp * coinToQ rewardPot
    _R = rewardPot - δt
    totalStake = maxSupply - reserves

getPoolRewardParameters ::
  (Ord p, Ord c, Show c) =>
  ProtocolParameters ->
  Pools p c ->
  BlocksMade p ->
  BlockCount ->
  Delgations p c ->
  StakeDistribution c ->
  Coin ->
  Coin ->
  Map (PoolID p) (PoolRewardInfo c)
getPoolRewardParameters pp pools blocks blocksTotal delegations sd totalStake r =
  Map.mapWithKey f pools
  where
    f = poolRewardInfo pp blocks blocksTotal sd delegations totalStake totA r
    totA = sum sd

computeMemberRewards' ::
  (Ord p, Ord c) =>
  Coin ->
  Map (PoolID p) (PoolRewardInfo c) ->
  Delgations p c ->
  StakeCredential c ->
  Coin ->
  Maybe Coin
computeMemberRewards' totalStake poolRIs ds sc c = do
  pid <- Map.lookup sc ds
  poolRI <- Map.lookup pid poolRIs
  if sc `Set.member` (owners . poolPs $ poolRI)
    then Nothing
    else Just $ memberRew
           (poolPot poolRI)
           (poolPs poolRI)
           (coinRatio c totalStake)
           (poolRelativeStake poolRI)

computeMemberRewards ::
  (Ord p, Ord c) =>
  Coin ->
  Map (PoolID p) (PoolRewardInfo c) ->
  Delgations p c ->
  StakeCredential c ->
  Coin ->
  Coin
computeMemberRewards totalStake poolRIs ds sc c =
  fromMaybe 0 $ computeMemberRewards' totalStake poolRIs ds sc c

rewards2 ::
  (Ord p, Ord c, Show c) =>
  ProtocolParameters ->
  Pools p c ->
  BlocksMade p ->
  Delgations p c ->
  StakeDistribution c ->
  Coin ->
  Coin ->
  Rewards c
rewards2 pp pools blocks delegations sd fees reserves = Map.unionWith (<>) mRs lRs
  where
    (r, totalStake, blocksTotal) = getRewardParameters pp blocks fees reserves
    poolInfos = getPoolRewardParameters pp pools blocks blocksTotal delegations sd totalStake r
    mRs = Map.mapWithKey (computeMemberRewards totalStake poolInfos delegations) sd
    f acc poolRI =
      Map.insertWith
        (<>)
        (poolSC . poolPs $ poolRI)
        (leaderRew
          (poolPot poolRI)
          (poolPs poolRI)
          (coinRatio (ownerStake poolRI) totalStake)
          (poolRelativeStake poolRI)
        )
        acc
    lRs = Map.foldl' f mempty poolInfos

-- Example --
aliceSC :: StakeCredential String
aliceSC = StakeCredential "alice"

bobSC :: StakeCredential String
bobSC = StakeCredential "bob"

carlSC :: StakeCredential String
carlSC = StakeCredential "carl"

ppEx :: ProtocolParameters
ppEx = ProtocolParameters
       { asc = 1 % 20
       , d = 1 % 100
       , κ = 2
       , ρ = 1 % 100
       , τ = 20 % 100
       }

poolsEx :: Pools String String
poolsEx =
  Map.fromList
   [ (PoolID "alice", PoolParameters 100 (50%100) 100 (Set.singleton aliceSC) aliceSC)
   , (PoolID "bob", PoolParameters 1 (50%100) 1000 (Set.singleton bobSC) bobSC)
   ]

blocksEx :: BlocksMade String
blocksEx =
  Map.fromList
    [ (PoolID "alice", 4)
    , (PoolID "bob", 2)
    ]

delegationsEx :: Delgations String String
delegationsEx =
  Map.fromList
   [ (aliceSC, PoolID "alice")
   , (carlSC, PoolID "alice")
   , (bobSC, PoolID "bob")
   ]
  
stakeEx :: StakeDistribution String
stakeEx =
  Map.fromList
   [ (aliceSC, 10000000)
   , (carlSC, 10000000)
   , (bobSC, 10000000)
   ]
  
feesEx :: Coin
feesEx = 100

reservesEx :: Coin
reservesEx = 1000000

example :: Rewards String
example = rewards ppEx poolsEx blocksEx delegationsEx stakeEx feesEx reservesEx

example2 :: Rewards String
example2 = rewards2 ppEx poolsEx blocksEx delegationsEx stakeEx feesEx reservesEx
