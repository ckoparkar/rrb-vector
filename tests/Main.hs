{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Main where

import Test.Tasty
import Test.Tasty.ExpectedFailure
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck
import Test.Tasty.TH


import qualified Data.RRB.Vector as V

--------------------------------------------------------------------------------

main :: IO ()
main = defaultMain allTests
  where allTests = testGroup "All" [ all_tests ]

all_tests :: TestTree
all_tests = $(testGroupGenerator)

-- Simple unit tests.
case_tolist_test1 :: Assertion
case_tolist_test1 = assertEqual "toList tree10 == [1..10]" (V.toList V.tree10) [1..10]

case_tolist_test2 :: Assertion
case_tolist_test2 = assertEqual "toList tree20 == [1..20]" (V.toList V.tree20) [1..20]

case_fromlist_test1 :: Assertion
case_fromlist_test1 = assertEqual "fromList [1..10] == tree10" (V.fromList [1..10]) V.tree10

case_fromlist_test2 :: Assertion
case_fromlist_test2 = assertEqual "fromList [1..20] == tree20" (V.fromList [1..20]) V.tree20

case_length_test1 :: Assertion
case_length_test1 = assertEqual "tree20" (V.length V.tree20) 20

case_get_singleton :: Assertion
case_get_singleton = assertEqual "[10] ! 0 == 10" ((V.fromList [10]) V.! 0) 10

-- Corner cases.
case_ub_get_test1 :: Assertion
case_ub_get_test1 = assertEqual "get" (map (V.tree_ub2 V.!) [0..9]) [1..10]

case_cons_new_root :: Assertion
case_cons_new_root = assertEqual "cons17" (V.cons (V.fromList [1..16]) 17) V.tree17_cons

case_snoc_new_root :: Assertion
case_snoc_new_root = assertEqual "snoc17" (V.snoc (V.fromList [1..16]) 17) V.tree17

case_get_too_big = assertEqual "[1..16] ! 3 == Nothing" ((V.fromList [1..16]) V.!? 16) Nothing

-- Some quickcheck tests.

prop_fromList_toList_inv :: [Int] -> Bool
prop_fromList_toList_inv ls = V.toList (V.fromList (ls :: [Int])) == ls

prop_length :: [Int] -> Bool
prop_length ls = length ls == V.length (V.fromList ls)

prop_get_null :: Int -> Bool
prop_get_null n = (V.empty :: V.Vector Int) V.!? n == Nothing

-- | Given a list of integers, and a valid index within that list,
--  check if a property holds.
qc_with_list_and_valid_index :: ([Int] -> Int -> Bool) -> Property
qc_with_list_and_valid_index fn =
  forAll num_gt_1
    (\n -> do let ls = [1..n]
              forAll (valid_indices_in ls)
                (\idx -> fn ls idx))

  where
    num_gt_1 = arbitrary `suchThat` (\n -> n > 1)
    valid_indices_in xs = elements (init xs)

prop_get_fromlist :: Property
prop_get_fromlist =
  qc_with_list_and_valid_index $
    \ls idx -> (V.fromList ls V.! idx) == (1 + idx)

prop_update :: Int -> Property
prop_update v =
  qc_with_list_and_valid_index $
    \ls idx -> let vec  = V.fromList ls
                   vec' = V.update vec idx v
               in vec' V.! idx == v

prop_concat :: Int -> Int -> Bool
prop_concat n m = (V.toList v_concat) == (ns ++ ms)
  where
    ns = [1..n]
    ms = [1..m]
    v_concat = V.fromList ns `V.concat` V.fromList ms
