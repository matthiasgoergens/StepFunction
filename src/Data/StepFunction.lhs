> {-# LANGUAGE PatternSynonyms, TypeFamilies #-}
> {-# LANGUAGE DeriveFunctor, DeriveGeneric, DeriveFoldable, DeriveTraversable #-}
> {-# LANGUAGE GeneralizedNewtypeDeriving, DeriveAnyClass #-}
> {-# LANGUAGE FlexibleInstances #-}
> {-# LANGUAGE MultiParamTypeClasses #-}
> {-# LANGUAGE ScopedTypeVariables #-}
> {-# LANGUAGE TypeOperators #-}
> {-# LANGUAGE PostfixOperators #-}
> {-# LANGUAGE TupleSections #-}
> module Data.StepFunction where
> import qualified Data.Map.Strict as DMS
> import Control.Applicative
> import Control.Lens.Indexed
> import Control.Monad.State.Strict
> import Control.Lens
> import Data.Maybe
> import GHC.Generics
> import Test.QuickCheck as QC
> import Prelude hiding (lookup)
> import Data.Bool

Module for stepfunctions.

Guiding principles
  like in Python's range function, intervals are half-open,
  [lo,hi) == {x | lo <= x < hi} that means half-open.

  'fn' turns step functions into proper Haskell functions.
  instances should commute with 'fn' where possible.  Ie type class instances
  are in analogue to the Reader Monad.

Lookup is via set operations on left-open half-lines:

{ x :: k | x < jump}

By default that only represent half open [) intervals, non-standard analysis
(or Dedekind cuts) inspire a trick: we extent our keys with an optional 'plus
epsilon'.  Thus:

    {x | lo + eps <= x <  hi + eps}
=== {x | lo       <  x <= hi }

(Adding the epsilon on the lo and hi sides have independent effects.)

Non-standard analysis would see complete (k, [Bool]) (or (k, [k]?),
but we only need first order epsilons, so we use:

> data Epsilon = Zero | Eps
>   deriving (Eq, Ord, Generic, Show)

> instance Arbitrary Epsilon where
>   arbitrary = QC.elements [Zero, Eps]
>   shrink Zero = []
>   shrink Eps = [Zero]
> instance CoArbitrary Epsilon

> data PlusEpsilon k = k :+! Epsilon
>   deriving (Eq, Ord, Functor, Generic, Show, Traversable, Foldable)

Same as normal +

> infixl 6 :+!

> instance Arbitrary k => Arbitrary (PlusEpsilon k) where
>   arbitrary = (:+!) <$> arbitrary <*> arbitrary
>   shrink = genericShrink
> instance CoArbitrary k => CoArbitrary (PlusEpsilon k)

Step function from k to a.  Same associativity and precedence as normal
function arrow.  Finite number of jumps.  (Haskell could support an infinite
number of jumps, but we are using Data.Map.Strict for the underlying
representation.)

> data (:->) k a = SF (DMS.Map (PlusEpsilon k) a) a
>   deriving (Eq, Ord, Functor, Generic, Show, Traversable, Foldable)
> infixr 0 :->
> type StepFunction k a = k :-> a

> instance (Ord k, Arbitrary k, Arbitrary a) => Arbitrary (k :-> a) where
>   arbitrary = SF <$> arbitrary <*> arbitrary
>   shrink = genericShrink

> instance (Monoid a, Ord k) => Monoid (k :-> a) where
>   mempty = pure mempty
>   mappend = liftA2 mappend

> type instance Index (k :-> a) = k
> type instance IxValue (k :-> a) = a
> instance Ord k => Ixed (k :-> a) where
>   ix k f m = f (fn m k) <&> \v' -> insert k v' m
>   {-# INLINE ix #-}

> instance (CoArbitrary k, CoArbitrary a) => CoArbitrary (k :-> a)

> data Bounds k = Lo | Val (PlusEpsilon k) | Hi
>   deriving (Eq, Ord, Show, Functor, Traversable, Foldable, Generic)
> type Interval k = (Bounds k, Bounds k)

> instance Arbitrary k => Arbitrary (Bounds k) where
>   arbitrary = oneof [pure Lo, Val <$> arbitrary, pure Hi]
>   shrink = genericShrink
> instance CoArbitrary k => CoArbitrary (Bounds k)

TODO: properties for itraverse?

 instance Ord k => TraversableWithIndex (Interval k) ((:->) k) where
   itraverse f = traverse (uncurry f) . giveBounds

 instance Ord k => FoldableWithIndex (Interval k) ((:->) k)
 instance Ord k => FunctorWithIndex (Interval k) ((:->) k)

TODO: add these:

 instance Ord k => At (k :-> a) where
   at k f m = f mv <&> \r -> case r of
     Nothing -> maybe m (const (Map.delete k m)) mv
     Just v' -> Map.insert k v' m
     where mv = Map.lookup k m
   {-# INLINE at #-}

 instance Eq e => Ixed (e -> a) where
  ix e p f = p (f e) <&> \a e' -> if e == e' then a else f e'
  {-# INLINE ix #-}

 instance Ord k => At (k :-> a) where
   at = undefined

> insert :: Ord k => k -> a -> (k :-> a) -> (k :-> a)
> insert k a s@(SF am atEnd) =
>   let (_, at, after) = lookup3 k s
>   in SF (DMS.insert (k :+! Zero) a . DMS.insert (k :+! Eps) after $ am) atEnd

> lookup :: Ord k => k -> (k :-> a) -> a
> lookup k = (\(_,m,_) -> m) . lookup3 k
> lookup' k (SF map end) = maybe end snd (DMS.lookupGE k map)

Lookup just before, at, and after:

> lookup3 :: Ord k => k -> (k :-> a) -> (a, a, a)
> lookup3 k (SF map end) =
>   ( maybe end snd (DMS.lookupGE (k :+! Zero) map)
>   , maybe end snd (DMS.lookupGE (k :+! Eps)  map)
>   , maybe end snd (DMS.lookupGT (k :+! Eps)  map))

> fn :: Ord k => (k :-> a) -> k -> a
> fn = flip lookup

> singleton def k a = interval def (k :+! Zero) (k :+! Eps) a

> jump left k right = SF (DMS.singleton k left) right
> jump' k = jump False k True

> interval def lo hi a | lo >= hi = SF DMS.empty def
> interval def lo hi a = SF (DMS.fromList [(lo, def), (hi, a)]) def
> interval' lo hi = interval False lo hi True

    [lo, hi + Eps)
=== [lo, hi]

> closedInterval lo hi = interval' (lo :+! Zero) (hi :+! Eps)

> instance (Ord k) => Applicative ((:->) k) where
>   pure = SF DMS.empty
>   SF fM f <*> SF aM a = SF `flip` f a $ DMS.fromDistinctAscList $ merge (DMS.toAscList fM) (DMS.toAscList aM) where
>     merge [] [] = []
>     merge [] aM = (fmap.fmap) f aM
>     merge fM [] = (fmap.fmap) ($ a) fM

This is where the decision to go with left-open half-lines really shines:

>     merge ((fk, f) : fs) ((ak, a) : as) = case compare fk ak of
>       LT -> (fk, f a) : merge fs             ((ak, a) : as)
>       EQ -> (fk, f a) : merge fs             as
>       GT -> (ak, f a) : merge ((fk, f) : fs) as

TODO: take from some common library

Todo: make nicer, perhaps?

> instance (Ord k) => Monad ((:->) k) where
>   s@(SF aM a) >>= f =
>     let SF bM b = fmap f s
>     in ifoldr fuse b bM

> giveLowerBound :: (k :-> a) -> k :-> (Maybe (PlusEpsilon k), a)
> giveLowerBound (SF map end) =
>   let (map', lastK) = runState (itraverse (\i a -> (,a) <$> swap (Just i)) map) Nothing
>       end' = (lastK, end)
>   in SF map' end'

> swap a = get <* put a

free applicative?

> (.:) = (.) . (.)

 restrictAll :: forall k a . Ord k => (k :-> (k :-> a)) -> k :-> k :-> a
 restrictAll sf =
   let SF map end = fmap (\(lo, a) -> maybe id onlyAfter lo a) $ giveLowerBound sf
   in SF (imap onlyBefore map) end

 break :: Ord k => PlusEpsilon k -> (k :-> a) -> (k :-> a, k :-> a)
 break k s = (onlyBefore k s, onlyAfter k s)
 onlyBefore, onlyAfter :: Ord k => PlusEpsilon k -> (k :-> a) -> (k :-> a)

 onlyAfter lo s@(SF aM atEnd) =
   let (_, after) = DMS.split lo aM
       at = lookup' lo s
   in SF (DMS.insert lo at after) atEnd

 onlyBefore hi s@(SF aM _) =
   let (lower, _) = DMS.split hi aM
       -- (atEnd, _, _) = lookup3 hi s
   in SF lower _

 lastDef :: a -> [a] -> a
 lastDef def xs = foldr cons id xs def where
   nil = id
   cons x rest def = rest x

This could be done better, staying in trees (Data.Map.Strict.Map) not going via List.

 giveBounds :: forall k a . Ord k => (k :-> a) -> k :-> (Interval k, a)
 giveBounds (SF aM atEnd) =
   let breaks :: [PlusEpsilon k]
       vs :: [a]
       (breaks, vs) = unzip $ DMS.toAscList aM
       aug :: Bounds k -> PlusEpsilon k -> a -> (PlusEpsilon k, (Interval k, a))
       aug lo hi v = (hi, ((lo, Val hi), v))
       atEnd' = ((lastDef Lo $ map Val breaks, Hi), atEnd)
       aM' :: DMS.Map (PlusEpsilon k) (Interval k, a)
       aM' = DMS.fromAscList $ zipWith3 aug (Lo : map Val breaks) breaks vs
   in SF aM' atEnd'

> smooth :: (Ord k, Eq a) => (k :-> a) -> (k :-> a)
> smooth (SF m a) =
>   let kas = DMS.toAscList m
>       out (k, a) a' | a == a' = Nothing
>                     | otherwise = Just (k, a)
>   in SF (DMS.fromAscList . catMaybes $ zipWith out kas (map snd (drop 1 kas) ++ [a])) a

> fuse :: Ord k => PlusEpsilon k -> (k :-> a) -> (k :-> a) -> (k :-> a)
> fuse k s@(SF lo _) (SF hi atEnd) =
>   let (lo', _) = DMS.split k lo
>       (_, hi') = DMS.split k hi
>       at       = lookup' k s
>   in SF (DMS.union lo' (DMS.insert k at hi')) atEnd

> breaks :: Ord k => (k :-> a) -> [PlusEpsilon k]
> breaks (SF aM _) = DMS.keys aM
