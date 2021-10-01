{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE EmptyDataDeriving #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Test.Cardano.Ledger.ModelChain.Value where

import Cardano.Ledger.Coin
import Cardano.Ledger.Val hiding (invert)
import Control.DeepSeq
import Control.Lens (Iso', Lens', at, iso, set)
import Control.Lens.Indexed (FoldableWithIndex (..), ifoldl)
import Control.Monad
import qualified Control.Monad.Except as Except
import Data.Coerce (coerce)
import Data.Functor.Const
import Data.Functor.Identity
import Data.Group (Abelian, Group (..))
import Data.Kind
import qualified Data.Map as Map
import qualified Data.Map.Merge.Lazy as MapLazy
import qualified Data.Map.Merge.Strict as Map
import Data.Monoid (All (..), Sum (..))
import GHC.Generics (Generic)
import qualified GHC.TypeLits as GHC
import Numeric.Natural

data ModelValueF (a :: Type) where
  ModelValue_Var :: a -> ModelValueF a
  ModelValue_Inject :: Coin -> ModelValueF a
  ModelValue_Scale :: Natural -> ModelValueF a -> ModelValueF a
  ModelValue_Add :: ModelValueF a -> ModelValueF a -> ModelValueF a
  ModelValue_Sub :: ModelValueF a -> ModelValueF a -> ModelValueF a
  deriving (Generic)

instance NFData a => NFData (ModelValueF a)

deriving instance Show a => Show (ModelValueF a)

deriving instance Eq a => Eq (ModelValueF a)

deriving instance Ord a => Ord (ModelValueF a)

deriving instance Functor ModelValueF

deriving instance Foldable ModelValueF

deriving instance Traversable ModelValueF

data ModelValueError a
  = ValueUnderflow a a
  deriving (Show)

-- TODO: monoidal-containers
newtype GrpMap k v = GrpMap {unGrpMap :: Map.Map k v}
  deriving (Foldable, Eq, Ord, Show, Generic)

instance (NFData k, NFData v) => NFData (GrpMap k v)

grpMapSingleton :: (Eq v, Monoid v) => k -> v -> GrpMap k v
grpMapSingleton k v
  | v == mempty = GrpMap Map.empty
  | otherwise = GrpMap $ Map.singleton k v

mkGrpMap :: (Eq v, Monoid v) => Map.Map k v -> GrpMap k v
mkGrpMap = GrpMap . Map.filter (mempty /=)

_GrpMap :: (Eq a, Monoid a) => Iso' (GrpMap k a) (Map.Map k a)
_GrpMap = iso unGrpMap mkGrpMap

grpMap :: (Ord k, Eq a, Monoid a) => k -> Lens' (GrpMap k a) a
grpMap k a2fb (GrpMap s) = (\y -> GrpMap $ set (at k) (y <$ guard (y /= mempty)) s) <$> a2fb (maybe mempty id $ Map.lookup k s)

instance GHC.TypeError ('GHC.Text "GrpMap is not a Functor, use mapGrpMap") => Functor (GrpMap k) where
  fmap = error "GrpMap is not a Functor, use mapGrpMap"

instance GHC.TypeError ('GHC.Text "GrpMap is not a Functor, use mapGrpMap") => Traversable (GrpMap k) where
  traverse = error "GrpMap is not Traversable, use traverseGrpMap"

mapGrpMap :: (Eq b, Monoid b) => (a -> b) -> GrpMap k a -> GrpMap k b
mapGrpMap f = GrpMap . Map.mapMaybe f' . unGrpMap
  where
    f' x = let y = f x in y <$ guard (y /= mempty)
{-# INLINE mapGrpMap #-}

-- | laws: traverseGrpMap (f . const mempty) xs === pure mempty
traverseGrpMap :: (Eq b, Monoid b, Applicative m) => (a -> m b) -> GrpMap k a -> m (GrpMap k b)
traverseGrpMap f = fmap GrpMap . Map.traverseMaybeWithKey f' . unGrpMap
  where
    f' _ x = (\y -> y <$ guard (y /= mempty)) <$> f x
{-# INLINE traverseGrpMap #-}

instance FoldableWithIndex k (GrpMap k) where
  ifoldMap f = ifoldMap f . unGrpMap

instance (Ord k, Eq v, Monoid v) => Semigroup (GrpMap k v) where
  GrpMap xs <> GrpMap ys = GrpMap $ Map.merge Map.preserveMissing Map.preserveMissing (Map.zipWithMaybeMatched f) xs ys
    where
      f _ x y = let z = x <> y in z <$ guard (z /= mempty)
  {-# INLINE (<>) #-}

instance (Ord k, Eq v, Monoid v) => Monoid (GrpMap k v) where
  mempty = GrpMap Map.empty
  {-# INLINE mempty #-}

instance (Ord k, Eq v, Group v) => Group (GrpMap k v) where
  invert = GrpMap . fmap invert . unGrpMap
  {-# INLINE invert #-}
  GrpMap xs ~~ GrpMap ys = GrpMap $ Map.merge Map.preserveMissing (Map.mapMissing $ const invert) (Map.zipWithMaybeMatched f) xs ys
    where
      f _ x y = let z = x ~~ y in z <$ guard (z /= mempty)
  {-# INLINE (~~) #-}

pointWise' :: Ord k => v -> (v -> v -> Bool) -> Map.Map k v -> Map.Map k v -> Bool
pointWise' z p = \xs ys ->
  getAll $! getConst $
    MapLazy.mergeA
      (MapLazy.traverseMissing $ \_ x -> Const $ All $ p x z)
      (MapLazy.traverseMissing $ \_ y -> Const $ All $ p z y)
      (MapLazy.zipWithAMatched $ \_ x y -> Const $ All $ p x y)
      xs
      ys
{-# INLINE pointWise' #-}

newtype ModelValueSimple a = ModelValueSimple {unModelValueSimple :: (Coin, GrpMap a (Sum Integer))}
  deriving (Eq, Ord, Show)

instance Ord a => Semigroup (ModelValueSimple a) where
  ModelValueSimple x <> ModelValueSimple y = ModelValueSimple (x <> y)

instance Ord a => Monoid (ModelValueSimple a) where
  mempty = ModelValueSimple mempty

instance Ord a => Group (ModelValueSimple a) where
  invert (ModelValueSimple x) = ModelValueSimple (invert x)
  ModelValueSimple x ~~ ModelValueSimple y = ModelValueSimple (x ~~ y)
  pow (ModelValueSimple x) = ModelValueSimple . pow x

instance Ord a => Abelian (ModelValueSimple a)

instance Ord a => Val (ModelValueSimple a) where
  -- these operations are kinda sus; represented variables can (and do)
  -- represent unknown qty of ADA, for the same reason that the question
  -- "How many prime factors does '15*y' have?", it has at least the factors of
  -- 15, but also, all of unknown factors of y.
  coin (ModelValueSimple (c, _)) = c
  modifyCoin f (ModelValueSimple (c, x)) = ModelValueSimple (f c, x)

  (<×>) = flip pow
  inject x = ModelValueSimple (x, mempty)
  size _ = 1
  pointwise f (ModelValueSimple (Coin x, y)) (ModelValueSimple (Coin x', y')) = f x x' && pointWise' 0 f (coerce y) (coerce y')

-- evaluate a modelValue and compute the linear sum of all free variables.  Not
-- unlike a MA token, but
evalModelValueSimple ::
  Ord a =>
  ModelValueF a ->
  Either
    (ModelValueError (ModelValueSimple a))
    (ModelValueSimple a)
evalModelValueSimple =
  runIdentity
    . evalModelValue (\x -> Identity $ ModelValueSimple (mempty, GrpMap (Map.singleton x 1)))

getModelValueSimple :: ModelValueSimple a -> (Coin, Map.Map a Integer)
getModelValueSimple =
  (fmap . fmap) getSum
    . fmap unGrpMap
    . unModelValueSimple

mkModelValue :: ModelValueSimple a -> ModelValueF a
mkModelValue = uncurry mkModelValue' . getModelValueSimple

mkModelValue' :: Integral i => Coin -> Map.Map a i -> ModelValueF a
mkModelValue' ada =
  ifoldl
    ( \v acc q ->
        if q >= 0
          then acc `ModelValue_Add` ModelValue_Scale (fromIntegral q) (ModelValue_Var v)
          else acc `ModelValue_Sub` ModelValue_Scale (fromIntegral (- q)) (ModelValue_Var v)
    )
    (ModelValue_Inject ada)

evalModelValue ::
  forall val m a.
  (Val val, Monad m) =>
  (a -> m val) ->
  ModelValueF a ->
  m (Either (ModelValueError val) val)
evalModelValue env x = Except.runExceptT (go x)
  where
    go :: ModelValueF a -> Except.ExceptT (ModelValueError val) m val
    go (ModelValue_Var a) = Except.lift $ env a
    go (ModelValue_Inject c) = pure (inject c)
    go (ModelValue_Add a b) = (<+>) <$> go a <*> go b
    go (ModelValue_Scale n a) = (toInteger n <×>) <$> go a
    go (ModelValue_Sub a b) = do
      a' <- go a
      b' <- go b
      unless (pointwise (>=) a' b') $ Except.throwError $ ValueUnderflow a' b'
      pure $ a' <-> b'
