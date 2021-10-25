{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Data.Compact.HashMap where

import Cardano.Crypto.Hash.Class
import Data.Compact.KeyMap (Key, KeyMap)
import qualified Data.Compact.KeyMap as KM
import Data.Proxy
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Typeable
import GHC.TypeLits

-- ==========================================================================

class Keyed t where
  toKey :: t -> Key
  fromKey :: Key -> t

instance HashAlgorithm h => Keyed (Hash h a) where
  toKey h =
    case hashToPackedBytes h of
      PackedBytes8 a -> KM.Key a 0 0 0
      PackedBytes28 a b c d -> KM.Key a b c (fromIntegral d)
      PackedBytes32 a b c d -> KM.Key a b c d
      _ -> error $ "Unsupported hash size: " <> show (sizeHash (Proxy :: Proxy h))
  fromKey (KM.Key a b c d) =
    hashFromPackedBytes $
      case sameNat (Proxy :: Proxy (SizeHash h)) (Proxy :: Proxy 32) of
        Just Refl -> PackedBytes32 a b c d
        Nothing ->
          case sameNat (Proxy :: Proxy (SizeHash h)) (Proxy :: Proxy 28) of
            Just Refl -> PackedBytes28 a b c (fromIntegral d)
            Nothing ->
              case sameNat (Proxy :: Proxy (SizeHash h)) (Proxy :: Proxy 8) of
                Just Refl -> PackedBytes8 a
                Nothing -> error $ "Unsupported hash size: " <> show (sizeHash (Proxy :: Proxy h))

data HashMap k v where
  HashMap :: Keyed k => KeyMap v -> HashMap k v

lookup :: k -> HashMap k v -> Maybe v
lookup k (HashMap m) = KM.lookupHM (toKey k) m

insert :: k -> v -> HashMap k v -> HashMap k v
insert k v (HashMap m) = HashMap (KM.insert (toKey k) v m)

insertWithKey :: (k -> v -> v -> v) -> k -> v -> HashMap k v -> HashMap k v
insertWithKey combine key v (HashMap m) = HashMap (KM.insertWithKey comb (toKey key) v m)
  where
    comb k v1 v2 = combine (fromKey k) v1 v2

restrictKeys :: HashMap k v -> Set k -> HashMap k v
restrictKeys (HashMap m) set = HashMap (KM.domainRestrict m (Set.map toKey set))

splitLookup :: k -> HashMap k a -> (HashMap k a, Maybe a, HashMap k a)
splitLookup k (HashMap m) = (HashMap a, b, HashMap c)
  where
    (a, b, c) = KM.splitKeyMap (KM.keyPath key) key m
    key = toKey k

intersection :: HashMap k v -> HashMap k v -> HashMap k v
intersection (HashMap m1) (HashMap m2) = HashMap (KM.intersect m1 m2)

foldlWithKey' :: (ans -> k -> v -> ans) -> ans -> HashMap k v -> ans
foldlWithKey' accum a (HashMap m) = KM.foldWithAscKey accum2 a m
  where
    accum2 ans k v = accum ans (fromKey k) v

size :: HashMap k v -> Int
size (HashMap m) = KM.sizeKeyMap m

fromList :: Keyed k => [(k, v)] -> HashMap k v
fromList xs = HashMap (KM.fromList (map (\(k, v) -> (toKey k, v)) xs))

toList :: HashMap k v -> [(k, v)]
toList (HashMap m) = KM.foldWithAscKey (\ans k v -> (fromKey k, v) : ans) [] m

mapWithKey :: (k -> v -> u) -> HashMap k v -> HashMap k u
mapWithKey f (HashMap m) = HashMap (KM.mapWithKey (\key v -> f (fromKey key) v) m)
