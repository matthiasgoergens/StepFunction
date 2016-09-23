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

> data SF k a = SF a (DMS.Map (IE k) a)
>   deriving (Functor, Generic, Show, Traversable, Foldable)

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
> type Interval k = (Bounds k, Bounds k)

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
> insert k a s@(SF minf am) =
>   let (_, at, after) = lookup3 k s
>   in SF minf . DMS.insert (k, False) a . DMS.insert (k, True) after $ am

> lookup :: Ord k => k -> SF k a -> a
> lookup k (SF def m) = maybe def snd (DMS.lookupLE (k, False) m)

Lookup just before, at, and after:

> lookup3 :: Ord k => k -> SF k a -> (a, a, a)
> lookup3 k (SF minf am) =
>   ( maybe minf snd (DMS.lookupLT (k, False) am)
>   , maybe minf snd (DMS.lookupLE (k, False) am)
>   , maybe minf snd (DMS.lookupLE (k, True)  am))

> fn :: Ord k => SF k a -> k -> a
> fn = flip lookup

> singleton def k a = interval def (k, False) (k, True) a

> jump left k right = SF left (DMS.singleton k right)
> jump' k = jump False k True

> interval def lo hi a | lo >= hi = SF def DMS.empty
> interval def lo hi a = SF def $ DMS.fromList [(lo, a), (hi, def)]
> interval' lo hi = interval False lo hi True

> closedInterval lo hi = interval' (lo, False) (hi, True)

> instance (Ord k) => Applicative (SF k) where
>   pure a = SF a DMS.empty
>   SF f fM <*> SF a aM = SF (f a) $ DMS.fromDistinctAscList $ merge f (DMS.toAscList fM) a (DMS.toAscList aM) where
>     merge f [] a [] = []
>     merge f [] _ aM = (fmap.fmap) f aM
>     merge f fM a [] = (fmap.fmap) ($ a) fM
>     merge f ((fM1k, fM1) : fMs) a ((aM1k, aM1) : aMs) = case compare fM1k aM1k of
>       LT -> (fM1k, fM1 a)   : merge fM1 fMs a ((aM1k, aM1) : aMs)
>       EQ -> (fM1k, fM1 aM1) : merge fM1 fMs aM1 aMs
>       GT -> (aM1k, f aM1)   : merge f ((fM1k, fM1) : fMs) aM1 aMs

> (.:) = (.) . (.)

Todo: make nicer, perhaps?

> instance (Ord k) => Monad (SF k) where
>   s@(SF a aM) >>= f =
>     let SF (SF b bM1) bM = fmap (uncurry restrict) $ giveBounds (fmap f s)
>         unSF (SF _ x) = x
>     in SF b $ DMS.unions (bM1 : fmap unSF (DMS.elems bM))

> restrict :: Ord k => Interval k -> SF k a -> SF k a
> restrict (lo, hi) = onlyAfter lo . onlyBefore hi

> break :: Ord k => Bounds k -> SF k a -> (SF k a, SF k a)
> break k s = (onlyBefore k s, onlyAfter k s)
> onlyBefore, onlyAfter :: Ord k => Bounds k -> SF k a -> SF k a

> onlyAfter Lo s = s
> onlyAfter (Val lo) (SF a aM) =
>   let (_, after) = DMS.split lo aM
>       at = maybe a snd . DMS.lookupLE lo $ aM
>   in SF at (DMS.insert lo at after)
> onlyAfter Hi (SF a aM) =
>   SF `flip` DMS.empty $ maybe a fst $ DMS.maxView aM

> onlyBefore Lo (SF a aM) = SF a DMS.empty
> onlyBefore (Val hi) (SF a aM) =
>   let (lower, _) = DMS.split hi aM
>   in SF a lower
> onlyBefore Hi s = s

> giveBounds :: forall k a . Ord k => SF k a -> SF k (Interval k, a)
> giveBounds (SF a aM) =
>   let breaks :: [IE k]
>       vs :: [a]
>       (breaks, vs) = unzip $ DMS.toAscList aM
>       aug :: IE k -> Bounds k -> a -> (IE k, (Interval k, a))
>       aug lo hi v = (lo, ((Val lo, hi), v))
>       a' = ((Lo, foldr (const . Val) Hi breaks), a)
>       aM' :: DMS.Map (IE k) (Interval k, a)
>       aM' = DMS.fromAscList $ zipWith3 aug breaks (map Val (drop 1 breaks) ++ [Hi]) vs
>   in SF a' aM'
