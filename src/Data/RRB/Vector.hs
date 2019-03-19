{-# OPTIONS_GHC -Wno-unused-top-binds #-}

module Data.RRB.Vector
  ( Vector , (!), update, snoc, concat
  , empty, toList, fromList, length ) where

import           Data.Bits
import           Debug.Trace
import           Prelude hiding (length, concat)
import qualified Prelude as P

--------------------------------------------------------------------------------

-- | Branching factor.
m :: Int
m = 4

log2m :: Int
log2m = round ((logBase 2 . realToFrac) m :: Float)

-- | Used by 'get' to traverse the tree.
mask :: Int
mask = m - 1

type Height = Int
type Size   = Int

-- | The main datatype.
data Tree a = Leaf [a]
            | Node { height   :: Height
                   , sizes    :: [Size]
                   , subtrees :: [Tree a] }
  deriving (Show, Read, Eq)

-- | A vector backed by a Radix-Balanced Tree.
type Vector a = Tree a

-- TODO: pretty printer.

----------------------------------------
-- Lookup
----------------------------------------

-- | O(log_m n) indexing.
(!) :: Vector a -> Int -> a
(!) = get

-- | O(log_m n) indexing.
get :: Vector a -> Int -> a
get tr idx =
  case tr of
    Leaf ns -> ns !! idx
    Node ht szs trs ->
      let (slot', idx') = indexInNode ht szs idx
      in get (trs !! slot') idx'

-- | Returns the position of the sub-tree to follow (while fetching/updating),
-- and the new index.
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

-- | O (m * (log_m n)) updates. However, this is not like the implementation
-- presented in the paper at all. It copies everything instead of using the ST
-- monad.
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
-- Insert front/back
----------------------------------------

-- | O (m * (log_m n)).
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
        Node ht [] [] -> let new_branch = mkLeafAtHeight (ht-1) v1
                         in Just $ Node ht [1] [new_branch]
        Node ht szs trs ->
          let bot_right = last trs
          in case tryBottomRight bot_right v1 of
                Just snocd -> let szs' = init szs
                                  trs' = init trs
                                  snocd_size = last szs + 1
                              in Just $ Node ht (szs' ++ [snocd_size]) (trs' ++ [snocd])
                Nothing    -> if P.length trs < m
                              then let new_branch = mkLeafAtHeight (ht-1) v1
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

-- | O(n) concatenation.
concat :: Vector a -> Vector a -> Vector a
concat a b = foldl snoc a (toList b)

----------------------------------------
-- Other common operations
----------------------------------------

-- | O(1) Empty vector.
empty :: Vector a
empty = Node 1 [] []

-- | O(n) Convert a list to a vector.
toList :: Vector a -> [a]
toList = go []
  where
    go :: [a] -> Vector a -> [a]
    go acc tr =
      case tr of
        Leaf ns -> acc ++ ns
        Node _ _ trs  -> foldl go acc trs

-- | O(n) Convert a vector to a list.
fromList :: [a] -> Vector a
fromList = foldl snoc empty

-- | Return the length of the vector, assuming that 'sizes' is never empty;
-- which is not how the paper uses it.
length :: Vector a -> Int
length tr =
  case tr of
    Leaf ns -> P.length ns
    Node{}  -> last $ sizes tr
