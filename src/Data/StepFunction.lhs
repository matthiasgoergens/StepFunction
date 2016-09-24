> {-# LANGUAGE PatternSynonyms, TypeFamilies #-}
> {-# LANGUAGE DeriveFunctor, DeriveGeneric, DeriveFoldable, DeriveTraversable #-}
> {-# LANGUAGE GeneralizedNewtypeDeriving, DeriveAnyClass #-}
> {-# LANGUAGE FlexibleInstances #-}
> {-# LANGUAGE MultiParamTypeClasses #-}
> {-# LANGUAGE ScopedTypeVariables #-}
> module Data.StepFunction where
> import qualified Data.Map.Strict as DMS
> import Control.Applicative
> import Control.Lens.Indexed
> import Control.Lens
> import Data.Maybe
> import GHC.Generics
> import Test.QuickCheck
> import Prelude hiding (lookup)
> import Data.Bool


Monoid Action: similar to group acting on set.

instance Monoid (m -> a -> a) where
  mempty = const id
  mappend m n = m . n

Look at semi-direct products for monoids acting on monoids.

Eg Offset Monoid acting on pointers or numbers.

type Offset = Sum Int

Obvious generalization: look at semiring actions in Haskell. (eg regular expressions)

Applicative=Monoidal functors are parameterized monoids!  (I saw that earlier at Google.)

Twisted-functor: semi-direct product for functors (=applicative functors)


Inclusion / Exclusion

> type IE k = (k, Bool)

StepFunction

> data SF k a = SF (DMS.Map (IE k) a) a
>   deriving (Eq, Ord, Functor, Generic, Show, Traversable, Foldable)

> instance (Ord k, Arbitrary k, Arbitrary a) => Arbitrary (SF k a) where
>   arbitrary = SF <$> arbitrary <*> arbitrary
>   shrink = genericShrink

> instance (Monoid a, Ord k) => Monoid (SF k a) where
>   mempty = pure mempty
>   mappend = liftA2 mappend

> type instance Index (SF k a) = k
> type instance IxValue (SF k a) = a
> instance Ord k => Ixed (SF k a) where
>   ix k f m = f (fn m k) <&> \v' -> insert k v' m
>   {-# INLINE ix #-}

> instance (CoArbitrary k, CoArbitrary a) => CoArbitrary (SF k a)

> data Bounds k = Lo | Val (IE k) | Hi
>   deriving (Eq, Ord, Show, Functor, Traversable, Foldable, Generic)
> type Interval k = (Bounds k, Bounds k)

> instance Arbitrary k => Arbitrary (Bounds k) where
>   arbitrary = oneof [pure Lo, Val <$> arbitrary, pure Hi]

> instance Ord k => TraversableWithIndex (Interval k) (SF k) where
>   itraverse f = traverse (uncurry f) . giveBounds
> instance Ord k => FoldableWithIndex (Interval k) (SF k)
> instance Ord k => FunctorWithIndex (Interval k) (SF k)

 instance Ord k => At (SF k a) where
   at k f m = f mv <&> \r -> case r of
     Nothing -> maybe m (const (Map.delete k m)) mv
     Just v' -> Map.insert k v' m
     where mv = Map.lookup k m
   {-# INLINE at #-}

 instance Eq e => Ixed (e -> a) where
  ix e p f = p (f e) <&> \a e' -> if e == e' then a else f e'
  {-# INLINE ix #-}

> instance Ord k => At (SF k a) where
>   at = undefined

> insert :: Ord k => k -> a -> SF k a -> SF k a
> insert k a s@(SF am atEnd) =
>   let (_, at, after) = lookup3 k s
>   in SF (DMS.insert (k, False) a . DMS.insert (k, True) after $ am) atEnd


k + ?epsilon

lookup k == x:


k <= x + epsilon <= k + epsilon

x <  k + ?epsilon

k + 0 < x < k + eps # wrong?
k + 0 < x + eps < k + eps + eps # bad?

> lookup :: Ord k => k -> SF k a -> a
> lookup k = (\(_,m,_) -> m) . lookup3 k

Lookup just before, at, and after:

> lookup3 :: Ord k => k -> SF k a -> (a, a, a)
> lookup3 k (SF am atEnd) =
>   ( maybe atEnd snd (DMS.lookupGE (k, False) am)
>   , maybe atEnd snd (DMS.lookupGE (k, True)  am)
>   , maybe atEnd snd (DMS.lookupGT (k, True)  am))

> fn :: Ord k => SF k a -> k -> a
> fn = flip lookup

> singleton def k a = interval def (k, False) (k, True) a

> jump left k right = SF (DMS.singleton k left) right
> jump' k = jump False k True

> interval def lo hi a | lo >= hi = SF DMS.empty def
> interval def lo hi a = SF (DMS.fromList [(lo, def), (hi, a)]) def
> interval' lo hi = interval False lo hi True

> closedInterval lo hi = interval' (lo, False) (hi, True)

> instance (Ord k) => Applicative (SF k) where
>   pure = SF DMS.empty
>   SF fM f <*> SF aM a = SF `flip` f a $ DMS.fromDistinctAscList $ merge (DMS.toAscList fM) (DMS.toAscList aM) where
>     merge [] [] = []
>     merge [] aM = (fmap.fmap) f aM
>     merge fM [] = (fmap.fmap) ($ a) fM
>     merge ((fk, f) : fs) ((ak, a) : as) = case compare fk ak of
>       LT -> (fk, f a) : merge fs             ((ak, a) : as)
>       EQ -> (fk, f a) : merge fs             as
>       GT -> (ak, f a) : merge ((fk, f) : fs) as

> (.:) = (.) . (.)

Todo: make nicer, perhaps?

> instance (Ord k) => Monad (SF k) where
>   s@(SF aM a) >>= f =
>     let SF bM (SF bM1 b) = fmap (uncurry restrict) $ giveBounds (fmap f s)
>         unSF (SF m _) = m
>     in SF (DMS.unions (bM1 : fmap unSF (DMS.elems bM))) b

> restrict :: Ord k => Interval k -> SF k a -> SF k a
> restrict (lo, hi) = onlyAfter lo . onlyBefore hi

> break :: Ord k => Bounds k -> SF k a -> (SF k a, SF k a)
> break k s = (onlyBefore k s, onlyAfter k s)
> onlyBefore, onlyAfter :: Ord k => Bounds k -> SF k a -> SF k a

> onlyAfter Lo s = s
> onlyAfter (Val lo) s@(SF aM atEnd) =
>   let (_, after) = DMS.split lo aM
>       at = maybe atEnd snd . DMS.lookupGE lo $ aM
>   in SF (DMS.insert lo at after) atEnd
> onlyAfter Hi (SF aM a) =
>   SF DMS.empty a

> onlyBefore Lo (SF aM atEnd) =
>   SF DMS.empty $ maybe atEnd fst $ DMS.minView aM
> onlyBefore (Val hi) (SF aM atEnd) =
>   let (lower, _) = DMS.split hi aM
>       at = maybe atEnd snd . DMS.lookupGE hi $ aM
>   in SF (DMS.insert hi at lower) atEnd
> onlyBefore Hi s = s

> lastDef :: a -> [a] -> a
> lastDef def xs = foldr cons id xs def where
>   nil = id
>   cons x rest def = rest x

This could be done better, staying in trees (Data.Map.Strict.Map) not going via List.

> giveBounds :: forall k a . Ord k => SF k a -> SF k (Interval k, a)
> giveBounds (SF aM atEnd) =
>   let breaks :: [IE k]
>       vs :: [a]
>       (breaks, vs) = unzip $ DMS.toAscList aM
>       aug :: Bounds k -> IE k -> a -> (IE k, (Interval k, a))
>       aug lo hi v = (hi, ((lo, Val hi), v))
>       atEnd' = ((lastDef Lo $ map Val breaks, Hi), atEnd)
>       aM' :: DMS.Map (IE k) (Interval k, a)
>       aM' = DMS.fromAscList $ zipWith3 aug (Lo : map Val breaks) breaks vs
>   in SF aM' atEnd'
