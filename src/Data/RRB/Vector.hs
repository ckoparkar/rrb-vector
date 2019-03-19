{-# OPTIONS_GHC -Wno-unused-top-binds #-}

module Data.RRB.Vector
  ( Vector , (!), get, snoc, length, update ) where

import           Data.Bits
import           Debug.Trace
import           Prelude hiding (length)
import qualified Prelude as P

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
            | Node { height   :: Height
                   , sizes    :: [Size]
                   , subtrees :: [Tree a] }
  deriving (Show, Read, Eq)

type Vector a = Tree a

----------------------------------------
-- Length
----------------------------------------

-- | Return the length of the vector, assuming that 'sizes' is never empty;
-- which is not how the paper uses it.
length :: Vector a -> Int
length tr =
  case tr of
    Leaf ns -> P.length ns
    Node{}  -> last $ sizes tr

----------------------------------------
-- Lookup
----------------------------------------

(!) :: Vector a -> Int -> a
(!) = get

get :: Vector a -> Int -> a
get tr idx =
  case tr of
    Leaf ns -> ns !! idx
    Node ht szs trs ->
      let (slot', idx') = indexInNode ht szs idx
      in get (trs !! slot') idx'

indexInNode :: Height -> [Size] -> Int -> (Int, Int)
indexInNode ht szs idx =
  let slot = index_of ht idx
      check_slot j = if idx >= (szs !! j)
                     then check_slot (j+1)
                     else j
      slot' = check_slot slot
      idx'  = idx - (if slot' == 0
                     then 0
                     else szs !! (slot' - 1))
  in (slot', idx')
  where
    index_of :: Height -> Int -> Int
    index_of ht1 i = quot i (m ^ ht1) `mod` m

    -- Calculate index using bit operations.
    _index_of' :: Height -> Int -> Int
    _index_of' ht1 i = shift i (-1 * ht1 * log2m) .&. mask

----------------------------------------
-- Update
----------------------------------------

-- This is not like the implementation presented in the paper at all.
-- It copies everything, no ST monad.
update :: Vector a -> Int -> a -> Vector a
update tr idx v =
  case tr of
    Leaf ns -> Leaf $ list_update_at ns idx v
    Node ht szs trs ->
      let (slot', idx') = indexInNode ht szs idx
          tr' = update (trs !! slot') idx' v
      in Node ht szs (list_update_at trs slot' tr')
  where
    -- | (list_update_at ls i v) == (ls[i] = v) in C.
    list_update_at :: [a] -> Int -> a -> [a]
    list_update_at xs i v1 = [ if j == i then v1 else x | (x,j) <- zip xs [0..] ]

----------------------------------------
-- Insert back/front
----------------------------------------

snoc :: Vector a -> a -> Vector a
snoc tr v =
  case tryBottomRight tr v of
    Just snocd -> snocd
    Nothing    -> join tr (mkLeafAtHeight (height tr) v)
  where
    tryBottomRight :: Vector a -> a -> Maybe (Vector a)
    tryBottomRight tr1 v1 =
      case tr1 of
        Leaf ns ->
          if P.length ns < m
          then Just $ Leaf (ns ++ [v1])
          else Nothing
        Node ht szs trs ->
          let bot_right = last trs
          in case tryBottomRight bot_right v1 of
                Just snocd -> let szs' = init szs
                                  trs' = init trs
                                  snocd_size = last szs + 1
                              in Just $ Node ht (szs' ++ [snocd_size]) (trs' ++ [snocd])
                Nothing    -> if P.length trs < m
                              then let new_branch = mkLeafAtHeight (ht-1) v1
                                       -- TODO: Is +1 ok here ?
                                   in Just $ Node ht (szs ++ [last szs + 1]) (trs ++ [new_branch])
                              else Nothing

    mkLeafAtHeight :: Height -> a -> Vector a
    mkLeafAtHeight ht v1 =
      if ht == 0
      then Leaf [v1]
      else Node ht [1] [mkLeafAtHeight (ht-1) v1]

-- | join a b, makes a & b siblings under a new root, assuming that
-- they're not leaves.
join :: Vector a -> Vector a -> Vector a
join a b = Node (height a + 1) [length a, length a + length b] [a,b]

----------------------------------------
-- Concat
----------------------------------------

concat :: Vector a -> Vector a -> Vector a
concat a b = _

--------------------------------------------------------------------------------

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


test1, test2, test3, test4, test5 :: Bool
test1 = tree_ub ! 20 == 21
test2 = tree_ub ! 2  == 3
test3 = tree_ub ! 6  == 7
test4 = tree10  ! 10 == 11
test5 = tree20  ! 20 == 21

all_tests :: Bool
all_tests = all (== True) [test1, test2, test3, test4, test5]
