{-# LANGUAGE TemplateHaskell #-}
import Data.StepFunction as S
import Test.QuickCheck
import Test.QuickCheck.Function
import Control.Monad
import Data.Foldable
import qualified Data.Map.Strict as DMS

prop_ap :: Int -> SF Int Int -> SF Int Int -> Property
prop_ap k f a =
  let g = fn ((,) <$> f <*> a)
      g' = (,) <$> fn f <*> fn a
  in g k === g' k

prop_join :: Int -> SF Int (SF Int Int) -> Property
prop_join k m =
  let m' = join m
      g  = fn m'
      g' = join . (.) fn . fn $ m
   in counterexample (show m')
   $ g' k === g k

prop_join2 :: SF Int Int -> Property
prop_join2 m =
  counterexample (show $ giveBounds m)
  $ counterexample (show . toList $ giveBounds m)
  $ m === (join . fmap pure) m

prop_onlyAfter :: Int -> SF Int Int -> Property
prop_onlyAfter cut m =
  let (before, at, after) = lookup3 cut (onlyAfter (Val (cut, True)) m)
  in before === at -- forgot the proper before.

prop_onlyBefore :: Int -> SF Int Int -> Property
prop_onlyBefore cut m =
  let oA = (onlyAfter (Val (cut, True)) m)
      (before, at, after) = lookup3 cut oA
  in counterexample (show oA)
  $ at === after -- forgot the proper after.

prop_break :: Bounds Int -> SF Int Int -> Property
prop_break cut m =
  let (SF lo _, SF hi atEnd) = S.break cut m
  in m === (SF (DMS.union lo hi) atEnd)

-- One of them also needs to forget the proper at.

prop_giveBounds :: Int -> Int -> Property
prop_giveBounds lo hi =
  lo < hi ==>
  let i = map fst . toList . giveBounds $ closedInterval lo hi
      lo' = Val (lo, False)
      hi' = Val (hi, True)
  in [(Lo, lo'), (lo', hi'), (hi', Hi)] === i

prop_singleton :: Int -> Int -> Property
prop_singleton q k =
  let s = singleton False k True
  in counterexample (show s)
  $ (q == k) === s `fn` q

prop_closedInterval :: Int -> Int -> Int -> Property
prop_closedInterval q lo hi =
  let i = closedInterval lo hi
  in counterexample (show i)
  $ (lo <= q && q <= hi) === fn i q

prop_closedIntervalSide :: Int -> Int -> Property
prop_closedIntervalSide lo hi =
  lo < hi ==>
  let i = closedInterval lo hi
  in counterexample (show i)
  $ (False, True, True) === lookup3 lo i
  .&. (True, True, False) === lookup3 hi i

prop_jump :: Int -> Int -> Int -> Property
prop_jump q lo hi =
  let c a b = a && not b
  in fn (closedInterval lo hi) q
  === fn (c <$> jump' (lo, False) <*> jump' (hi, True)) q

prop_lookup3_insert :: Int -> Int -> Property
prop_lookup3_insert q k = lookup3 q (singleton False q True) === (False, True, False)

return []

main :: IO Bool
main = $quickCheckAll
