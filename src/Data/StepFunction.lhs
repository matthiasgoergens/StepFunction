> {-# LANGUAGE PatternSynonyms, TypeFamilies #-}
> {-# LANGUAGE DeriveFunctor, DeriveGeneric, DeriveFoldable, DeriveTraversable #-}
> {-# LANGUAGE GeneralizedNewtypeDeriving, DeriveAnyClass #-}
> {-# LANGUAGE FlexibleInstances #-}
> {-# LANGUAGE MultiParamTypeClasses #-}
> {-# LANGUAGE ScopedTypeVariables #-}
> {-# LANGUAGE TypeOperators #-}
> {-# LANGUAGE PostfixOperators #-}
> module Data.StepFunction where
> import qualified Data.Map.Strict as DMS
> import Control.Applicative
> import Control.Lens.Indexed
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

By default we can only represent half open [) intervals, non-standard analysis
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
function arrow.

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

> instance Ord k => TraversableWithIndex (Interval k) ((:->) k) where
>   itraverse f = traverse (uncurry f) . giveBounds
> instance Ord k => FoldableWithIndex (Interval k) ((:->) k)
> instance Ord k => FunctorWithIndex (Interval k) ((:->) k)

 instance Ord k => At (k :-> a) where
   at k f m = f mv <&> \r -> case r of
     Nothing -> maybe m (const (Map.delete k m)) mv
     Just v' -> Map.insert k v' m
     where mv = Map.lookup k m
   {-# INLINE at #-}

 instance Eq e => Ixed (e -> a) where
  ix e p f = p (f e) <&> \a e' -> if e == e' then a else f e'
  {-# INLINE ix #-}

> instance Ord k => At (k :-> a) where
>   at = undefined

> insert :: Ord k => k -> a -> (k :-> a) -> (k :-> a)
> insert k a s@(SF am atEnd) =
>   let (_, at, after) = lookup3 k s
>   in SF (DMS.insert (k :+! Zero) a . DMS.insert (k :+! Eps) after $ am) atEnd


k + ?epsilon

lookup k == x:


k <= x + epsilon <= k + epsilon

x <  k + ?epsilon

k + 0 < x < k + eps # wrong?
k + 0 < x + eps < k + eps + eps # bad?

> lookup :: Ord k => k -> (k :-> a) -> a
> lookup k = (\(_,m,_) -> m) . lookup3 k

Lookup just before, at, and after:

> lookup3 :: Ord k => k -> (k :-> a) -> (a, a, a)
> lookup3 k (SF am atEnd) =
>   ( maybe atEnd snd (DMS.lookupGE (k :+! Zero) am)
>   , maybe atEnd snd (DMS.lookupGE (k :+! Eps)  am)
>   , maybe atEnd snd (DMS.lookupGT (k :+! Eps)  am))

> fn :: Ord k => (k :-> a) -> k -> a
> fn = flip lookup

> singleton def k a = interval def (k :+! Zero) (k :+! Eps) a

> jump left k right = SF (DMS.singleton k left) right
> jump' k = jump False k True

> interval def lo hi a | lo >= hi = SF DMS.empty def
> interval def lo hi a = SF (DMS.fromList [(lo, def), (hi, a)]) def
> interval' lo hi = interval False lo hi True

> closedInterval lo hi = interval' (lo :+! Zero) (hi :+! Eps)

> instance (Ord k) => Applicative ((:->) k) where
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

> instance (Ord k) => Monad ((:->) k) where
>   s@(SF aM a) >>= f =
>     let SF bM (SF bM1 b) = fmap (uncurry restrict) $ giveBounds (fmap f s)
>         unSF (SF m _) = m
>     in SF (DMS.unions (bM1 : fmap unSF (DMS.elems bM))) b

> restrict :: Ord k => Interval k -> (k :-> a) -> (k :-> a)
> restrict (lo, hi) = onlyAfter lo . onlyBefore hi

> break :: Ord k => Bounds k -> (k :-> a) -> (k :-> a, k :-> a)
> break k s = (onlyBefore k s, onlyAfter k s)
> onlyBefore, onlyAfter :: Ord k => Bounds k -> (k :-> a) -> (k :-> a)

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
>   in SF lower atEnd
> onlyBefore Hi s = s

> lastDef :: a -> [a] -> a
> lastDef def xs = foldr cons id xs def where
>   nil = id
>   cons x rest def = rest x

This could be done better, staying in trees (Data.Map.Strict.Map) not going via List.

> giveBounds :: forall k a . Ord k => (k :-> a) -> k :-> (Interval k, a)
> giveBounds (SF aM atEnd) =
>   let breaks :: [PlusEpsilon k]
>       vs :: [a]
>       (breaks, vs) = unzip $ DMS.toAscList aM
>       aug :: Bounds k -> PlusEpsilon k -> a -> (PlusEpsilon k, (Interval k, a))
>       aug lo hi v = (hi, ((lo, Val hi), v))
>       atEnd' = ((lastDef Lo $ map Val breaks, Hi), atEnd)
>       aM' :: DMS.Map (PlusEpsilon k) (Interval k, a)
>       aM' = DMS.fromAscList $ zipWith3 aug (Lo : map Val breaks) breaks vs
>   in SF aM' atEnd'

> smooth :: (Ord k, Eq a) => (k :-> a) -> (k :-> a)
> smooth (SF m a) =
>   let kas = DMS.toAscList m
>       out (k, a) a' | a == a' = Nothing
>                     | otherwise = Just (k, a)
>   in SF (DMS.fromAscList . catMaybes $ zipWith out kas (map snd (drop 1 kas) ++ [a])) a

> fuse :: Ord k => (k :-> a) -> (k :-> a) -> (k :-> a)
> fuse (SF lo _) (SF hi atEnd) = SF (DMS.union lo hi) atEnd

> breaks :: Ord k => (k :-> a) -> [PlusEpsilon k]
> breaks (SF aM _) = DMS.keys aM
