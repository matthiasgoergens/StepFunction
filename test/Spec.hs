{-# LANGUAGE TemplateHaskell #-}
import Data.StepFunction as S
import Test.QuickCheck
import Test.QuickCheck.Function
import Control.Monad

prop_ap :: Int -> SF Int Int -> SF Int Int -> Property
prop_ap k f a =
  let g = fn ((,) <$> f <*> a)
      g' = (,) <$> fn f <*> fn a
  in g k === g' k

prop_join :: Int -> SF Int (SF Int Int) -> Property
prop_join k m =
  let g  = fn (join m)
      g' = fn <=< fn $ m
   in g k === g' k

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

prop_jump :: Int -> Int -> Int -> Property
prop_jump q lo hi =
  let c a b = a && not b
  in fn (closedInterval lo hi) q 
  === fn (c <$> jump' (lo, False) <*> jump' (hi, True)) q

return []

main :: IO Bool
main = $quickCheckAll
