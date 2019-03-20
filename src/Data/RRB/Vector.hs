{-# OPTIONS_GHC -Wno-unused-top-binds #-}

-- | An implementation of vectors backed by a Radix-Balanced Tree.

module Data.RRB.Vector
  ( Vector , (!), (!?), update, cons, snoc, concat
  , empty, toList, fromList, length

  , -- * Some pre-defined testing data
    tree10, tree20, tree_ub, tree_ub2, tree17, tree17_cons
  ) where

import           Data.Bits
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

-- TODO: 'Show' is leaky. And a pretty printer.

----------------------------------------
-- Lookup
----------------------------------------

-- | O(log_m n) indexing.
(!) :: Vector a -> Int -> a
(!) tr idx =
  case mb_get tr idx of
    Left err -> error err
    Right x  -> x

-- | O(log_m n) safe indexing.
(!?) :: Vector a -> Int -> Maybe a
(!?) tr idx =
  case mb_get tr idx of
    Left{}  -> Nothing
    Right x -> Just x

mb_get :: Vector a -> Int -> Either String a
mb_get tr idx
  | not is_idx_valid = Left $ "(!): Index " ++ show idx ++ " is out of range (0," ++ show len  ++ ")"
  | otherwise =
      case tr of
        Leaf ns -> Right $ ns !! idx
        Node ht szs trs ->
          let (slot', idx') = indexInNode ht szs idx
          in mb_get (trs !! slot') idx'

  where len = length tr
        is_idx_valid = idx >= 0 && idx < len

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

-- | O(m * (log_m n)) updates. However, this is not like the implementation
-- presented in the paper at all. It copies everything instead of using the ST
-- monad.
update :: Vector a -> Int -> a -> Vector a
update tr idx v
  | not is_idx_valid = error $ "update: Index " ++ show idx ++ " is out of range (0," ++ show len  ++ ")"
  | otherwise =
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

    len = length tr
    is_idx_valid = idx >= 0 && idx < len

----------------------------------------
-- Insert front/back
----------------------------------------

data Where = Front | Back
  deriving Eq

-- | O(m * (log_m n)) Prepend an element.
cons  :: Vector a -> a -> Vector a
cons = insert Front

-- | O(m * (log_m n)) Append an element.
snoc  :: Vector a -> a -> Vector a
snoc = insert Back


insert :: Where -> Vector a -> a -> Vector a
insert whr tr v =
  case tryBottom tr v of
    Just has_v -> has_v
    Nothing    -> case whr of
                    Front -> join (mkLeafAtHeight (height tr) v) tr
                    Back  -> join tr (mkLeafAtHeight (height tr) v)
  where
    tryBottom :: Vector a -> a -> Maybe (Vector a)
    tryBottom tr1 v1 =
      case tr1 of
        Leaf ns
          | P.length ns < m ->
              case whr of
                Front -> Just $ Leaf (v1 : ns)
                Back  -> Just $ Leaf (ns ++ [v1])
          | otherwise -> Nothing

        -- The empty tree.
        Node ht [] [] -> Just $ Node ht [1] [mkLeafAtHeight (ht-1) v1]

        Node ht szs trs ->
          let node_to_try = case whr of
                              Front -> head trs
                              Back  -> last trs
          in case tryBottom node_to_try v1 of
               Just has_v -> let szs' = case whr of
                                          Front -> (1 + head szs) : tail szs
                                          Back  -> init szs ++ [1 + last szs]
                                 trs' = case whr of
                                          Front -> has_v : (tail trs)
                                          Back  -> init trs ++ [has_v]
                             in Just $ Node ht szs' trs'

               Nothing
                 | P.length trs < m ->
                   let branch = mkLeafAtHeight (ht-1) v1
                       szs'   = case whr of
                                      Front -> 1 : map (+1) szs
                                      Back  -> szs ++ [1 + last szs]
                       trs'   = case whr of
                                      Front -> branch : trs
                                      Back  -> trs ++ [branch]
                   in Just $ Node ht szs' trs'
                 | otherwise -> Nothing


    mkLeafAtHeight :: Height -> a -> Vector a
    mkLeafAtHeight ht v1
      | ht == 0   = Leaf [v1]
      | otherwise = Node ht [1] [mkLeafAtHeight (ht-1) v1]

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

-- | O(1) Return the length of the vector, assuming that 'sizes' is never empty.
-- Note that the paper does not use 'sizes' like this.
length :: Vector a -> Int
length tr =
  case tr of
    Leaf ns -> P.length ns
    Node _ szs _
      | null szs  -> 0
      | otherwise -> last szs

--------------------------------------------------------------------------------
-- Some pre-defined testing data.

tree10 :: Vector Int
tree10 = Node 1 [4,8,10]
                [ Leaf [1,2,3,4]
                , Leaf [5,6,7,8]
                , Leaf [9,10]
                ]

tree20 :: Vector Int
tree20 = Node 2 [16,20]
                [ Node 1 [4,8,12,16]
                         [ Leaf [1,2,3,4]
                         , Leaf [5,6,7,8]
                         , Leaf [9,10,11,12]
                         , Leaf [13,14,15,16]
                         ]
                , Node 1 [4]
                         [ Leaf [17,18,19,20]
                         ]
                ]

tree_ub :: Vector Int
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

tree_ub2 :: Vector Int
tree_ub2 = Node 1 [1,3,6,10]
                [ Leaf [1]
                , Leaf [2,3]
                , Leaf [4,5,6]
                , Leaf [7,8,9,10]
                ]


tree17 :: Vector Int
tree17 = Node 2 [16,17]
                [ Node 1 [4,8,12,16]
                         [ Leaf [1,2,3,4]
                         , Leaf [5,6,7,8]
                         , Leaf [9,10,11,12]
                         , Leaf [13,14,15,16]
                         ]
                , Node 1 [1]
                         [ Leaf [17]
                         ]
                ]


tree17_cons :: Vector Int
tree17_cons = Node 2 [1,17]
                [ Node 1 [1]
                         [ Leaf [17] ]
                , Node 1 [4,8,12,16]
                         [ Leaf [1,2,3,4]
                         , Leaf [5,6,7,8]
                         , Leaf [9,10,11,12]
                         , Leaf [13,14,15,16]
                         ]
                ]
