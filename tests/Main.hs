{-# LANGUAGE TemplateHaskell #-}

module Main where

import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.TH


import Data.RRB.Vector

--------------------------------------------------------------------------------

main :: IO ()
main = defaultMain allTests
  where allTests = testGroup "All" [ all_tests ]

all_tests :: TestTree
all_tests = $(testGroupGenerator)

--------------------------------------------------------------------------------

-- Some pre-defined trees for testing.

tree10 :: Tree Int
tree10 = Node 1 [4,8,11]
                [ Leaf [1,2,3,4]
                , Leaf [5,6,7,8]
                , Leaf [9,10,11]
                ]

tree20 :: Tree Int
tree20 = Node 2 [16,21]
                [ Node 1 [4,8,12,16]
                         [ Leaf [1,2,3,4]
                         , Leaf [5,6,7,8]
                         , Leaf [9,10,11,12]
                         , Leaf [13,14,15,16]
                         ]
                , Node 1 [4,5]
                         [ Leaf [17,18,19,20]
                         , Leaf [21]
                         ]
                ]

tree_ub :: Tree Int
tree_ub = Node 2 [9, 21]
                 [ Node 1 [3,6,9]
                             [ Leaf [1,2,3]
                             , Leaf [4,5,6]
                             , Leaf [7,8,9]
                             ]
                 , Node 1 [3,6,10,12]
                          [ Leaf [10,11,12]
                          , Leaf [13,14,15]
                          , Leaf [16,17,18,19]
                          , Leaf [20,21]]
                 ]


case_test1 :: Assertion
case_test1 = assertEqual "for (foo 3)," (1,2) (1,2)

-- test1, test2, test3, test4, test5 :: Bool
-- test1 = tree_ub ! 20 == 21
-- test2 = tree_ub ! 2  == 3
-- test3 = tree_ub ! 6  == 7
-- test4 = tree10  ! 10 == 11
-- test5 = tree20  ! 20 == 21

-- all_tests :: Bool
-- all_tests = all (== True) [test1, test2, test3, test4, test5]
