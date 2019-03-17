module Data.RRB.Vector where

import Data.Bits
import Debug.Trace

--------------------------------------------------------------------------------

-- | Branching factor.
m :: Int
m = 4

-- |
log2m :: Int
log2m = 2

-- |
mask :: Int
mask = m - 1

type Height = Int
type Size   = Int

data Tree a = Leaf [a]
            | Node Height [Size] [Tree a]
  deriving (Show, Read, Eq)


(!) :: Show a => Tree a -> Int -> a
(!) = get

get :: Show a => Tree a -> Int -> a
get tr idx =
  case tr of
    Leaf ns -> ns !! idx
    Node ht szs trs ->
      let slot = index_of ht idx
          check_slot j = if idx >= (szs !! j)
                         then check_slot (j+1)
                         else j
          slot' = check_slot slot
          idx'  = idx - (if slot' == 0
                         then 0
                         else szs !! (slot' - 1))
      in get (trs !! slot') idx'


index_of :: Height -> Int -> Int
index_of ht i = quot i (m ^ ht) `mod` m

-- Calculate index using bit operations.
index_of' :: Height -> Int -> Int
index_of' ht i = shift i (-1 * ht * log2m) .&. mask

--------------------------------------------------------------------------------

tree10 :: Tree Int
tree10 = Node 1 [4,8,11]
                [ Leaf [0,1,2,3]
                , Leaf [4,5,6,7]
                , Leaf [8,9,10]
                ]

tree20 :: Tree Int
tree20 = Node 2 [16,21]
                [ Node 1 [4,8,12,16]
                         [ Leaf [0,1,2,3]
                         , Leaf [4,5,6,7]
                         , Leaf [8,9,10,11]
                         , Leaf [12,13,14,15]
                         ]
                , Node 1 [4,5]
                         [ Leaf [16,17,18,19]
                         , Leaf [20]
                         ]
                ]

tree_ub :: Tree Int
tree_ub = Node 2 [9, 21]
                 [ Node 1 [2,6,9]
                             [ Leaf [0,1]
                             , Leaf [2,3,4,5]
                             , Leaf [6,7,8]
                             ]
                 , Node 1 [2,5,8,12]
                          [ Leaf [9,10]
                          , Leaf [11,12,13]
                          , Leaf [14,15,16]
                          , Leaf [17,18,19,20]]
                 ]


test1, test2, test3, test4, test5 :: Bool
test1 = tree_ub ! 20 == 20
test2 = tree_ub ! 2  == 2
test3 = tree_ub ! 6  == 6
test4 = tree10  ! 10 == 10
test5 = tree20  ! 20 == 20

all_tests :: Bool
all_tests = all (== True) [test1, test2, test3, test4, test5]
