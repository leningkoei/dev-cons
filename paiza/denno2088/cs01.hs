module Main where

-- import Debug.Trace qualified as DT

-- import Data.Set qualified as DS
-- import qualified Data.Set as DS

-- import Control.Monad qualified as CM
-- import Control.Monad.ST qualified as CMS
-- import Data.Array.IArray qualified as DAI
-- import Data.Array.MArray qualified as DAM
-- import Data.Array.ST qualified as DAS
-- import Data.Sequence qualified
-- import Data.Sequence qualified as DS
-- import Data.Sequence ((|>), ViewL ((:<)))

import qualified Control.Monad as CM
import qualified Control.Monad.ST as CMS
import qualified Data.Array.IArray as DAI
import qualified Data.Array.MArray as DAM
import qualified Data.Array.ST as DAS
import qualified Data.Sequence
import qualified Data.Sequence as DS
import Data.Sequence ((|>), ViewL ((:<)))

-- traceTaged :: Show a => String -> a -> a
-- traceTaged tag x = DT.trace (tag ++ ": " ++ show x) x

main :: IO ()
main = r >>= return . e >>= p

p :: Show a => a -> IO ()
p = print

--       h    w    areas of gang
r :: IO (Int, Int, [(Int, Int, Int)])
r = do
  [h, w, n] <- map read . words <$> getLine
  areas <- loop n
  return (h, w, areas)
  where
    loop :: Int -> IO [(Int, Int, Int)]
    loop 0 = return []
    loop n = do
      [y, x, s] <- map read . words <$> getLine
      areas <- loop (n - 1)
      return $ (y, x, s) : areas

type Matrix s = DAS.STArray s (Int, Int) Bool
data Elem = LevelEnd | Coordinate (Int, Int) deriving (Show, Eq)
-- e :: (Int, Int, [(Int, Int, Int)]) -> DAI.Array (Int, Int) Bool
-- e (h, w, areas) = DAS.runSTArray mMatrix where
--   mMatrix :: CMS.ST s (Matrix s)
--   mMatrix = do
e :: (Int, Int, [(Int, Int, Int)]) -> Int
e (h, w, areas) =  CMS.runST result where
 result :: CMS.ST s (Int)
 result = do
    matrix <- DAM.newArray ((1, 1), (h, w)) True
    occupy (Data.Sequence.fromList areas) matrix
    -- return matrix
    occupyed
      <- map (Coordinate . fst)
      . filter (not . snd)
      <$> DAM.getAssocs matrix
    expand ((Data.Sequence.fromList occupyed) |> LevelEnd) matrix
    where
      occupy :: DS.Seq (Int, Int, Int) -> Matrix s -> CMS.ST s ()
      occupy areas matrix
        | null areas = return ()
        | otherwise = do
          free <- DAM.readArray matrix (y, x)
          CM.when free $ DAM.writeArray matrix (y, x) False
          occupy (if free then areas' else rest) matrix
        where
          (y, x, s) :< rest = DS.viewl areas
          directions = filter (\ (y, x, s) ->
            s > -1 && y >= 1 && y <= h && x >= 1 && x <= w) $
            [ (y, x - 1, s - 1), (y, x + 1, s - 1)
            , (y - 1, x, s - 1), (y + 1, x, s - 1) ]
          areas' = foldr (flip (|>)) rest directions
      expand :: DS.Seq Elem -> Matrix s -> CMS.ST s (Int)
      expand edge matrix
        | DS.length edge <= 1 = return (-1)
        | current == LevelEnd = (+1) <$> expand (rest |> LevelEnd) matrix
        | otherwise = do
            let Coordinate (y, x) = current
            let directions = filter
                  (\ (y, x) -> y >= 1 && y <= h && x >= 1 && x <= w)
                  [(y, x - 1), (y, x + 1), (y - 1, x), (y + 1, x)]
            directions' <- CM.filterM
                  (\ (y, x) -> DAM.readArray matrix (y, x))
                  directions
            CM.forM_ directions' $ \ coordinate ->
              DAM.writeArray matrix coordinate False
            let edge' = foldr (flip (|>) . Coordinate) rest directions'
            expand edge' matrix
        where
          current :< rest = DS.viewl $ edge

-- e :: (Int, Int, [(Int, Int, Int)]) -> Int
-- e (h, w, area) = expand matrix' where
--   matrix = DS.fromList [(True, y, x) | y <- [1..h], x <- [1..w]]
--   matrix' = occupy DS.empty area matrix
--   occupy :: DS.Set (Int, Int) -> [(Int, Int, Int)] -> DS.Set (Bool, Int, Int) -> DS.Set (Bool, Int, Int)
--   occupy memo areas matrix
--     | null areas = matrix
--     | otherwise = occupy memo' areas'' matrix'
--     where
--       areas'
--         = filter (\ (y, x, _) -> (y, x) `DS.notMember` memo)
--         . filter (\ (_, _, s) -> s /= -1)
--         $ areas
--       matrix' = foldr f matrix areas'
--       f (y, x, _) matrix = modify (True, y, x) (False, y, x) matrix
--       memo' = DS.union memo . DS.fromList . map (\ (y, x, _) -> (y, x)) $ areas'
--       areas'' = foldr g [] areas'
--       g (y, x, s) areas''
--         = (y, x - 1, s - 1)
--         : (y, x + 1, s - 1)
--         : (y - 1, x, s - 1)
--         : (y + 1, x, s - 1)
--         : areas''
--   frees = DS.filter (\ (free, _, _) -> free)
--   occupyeds = DS.filter (\ (free, _, _) -> not free)
--   expand :: DS.Set (Bool, Int, Int) -> Int
--   expand matrix
--     | null . frees $ matrix = -1
--     | otherwise = 1 + expand matrix'
--     where
--       matrix' = foldr f matrix $ occupyeds matrix
--       f :: (Bool, Int, Int) -> DS.Set (Bool, Int, Int) -> DS.Set (Bool, Int, Int)
--       f (_, y, x)
--         = modify (True, y, x - 1) (False, y, x - 1)
--         . modify (True, y, x + 1) (False, y, x + 1)
--         . modify (True, y - 1, x) (False, y - 1, x)
--         . modify (True, y + 1, x) (False, y + 1, x)

-- e :: (Int, Int, [(Int, Int, Int)]) -> Int
-- e (h, w, area) = expand matrix' 0 where
--   matrix = DS.fromList [(99999, y, x) | y <- [1..h], x <- [1..w]]
--   matrix' = foldr occupy matrix area
--   occupy :: (Int, Int, Int) -> DS.Set (Int, Int, Int) -> DS.Set (Int, Int, Int)
--   occupy (y, x, s)
--     | s == -1 = id
--     | otherwise
--       = occupy (y, x - 1, s - 1)
--       . occupy (y, x + 1, s - 1)
--       . occupy (y - 1, x, s - 1)
--       . occupy (y + 1, x, s - 1)
--       . modify (99999, y, x) (-1, y, x)
--   frees = DS.filter (\ (free, _, _) -> free == 99999)
--   occupyeds = DS.filter (\ (free, _, _) -> free /= 99999)
--   expand :: DS.Set (Int, Int, Int) -> Int -> Int
--   expand matrix id
--     | null . frees $ matrix = -1
--     | otherwise = 1 + expand matrix' (id + 1)
--     where
--       edge = DS.filter (\ (lv, _, _) -> lv == id - 1) . occupyeds $ matrix
--       matrix' = foldr f matrix edge
--       f :: (Int, Int, Int) -> DS.Set (Int, Int, Int) -> DS.Set (Int, Int, Int)
--       f (_, y, x)
--         = modify (99999, y, x - 1) (id, y, x - 1)
--         . modify (99999, y, x + 1) (id, y, x + 1)
--         . modify (99999, y - 1, x) (id, y - 1, x)
--         . modify (99999, y + 1, x) (id, y + 1, x)

-- e :: (Int, Int, [(Int, Int, Int)]) -> Int
-- e (h, w, area) = expand matrix' where
--   matrix = DS.fromList [(True, y, x) | y <- [1..h], x <- [1..w]]
--   matrix' = foldr occupy matrix area
--   occupy :: (Int, Int, Int) -> DS.Set (Bool, Int, Int) -> DS.Set (Bool, Int, Int)
--   occupy (y, x, s)
--     | s == -1 = id
--     | otherwise
--       = occupy (y, x - 1, s - 1)
--       . occupy (y, x + 1, s - 1)
--       . occupy (y - 1, x, s - 1)
--       . occupy (y + 1, x, s - 1)
--       . modify (True, y, x) (False, y, x)
--   frees = DS.filter (\ (free, _, _) -> free)
--   occupyeds = DS.filter (\ (free, _, _) -> not free)
--   expand :: DS.Set (Bool, Int, Int) -> Int
--   expand matrix
--     | null . frees $ matrix = -1
--     | otherwise = 1 + expand matrix'
--     where
--       matrix' = foldr f matrix $ occupyeds matrix
--       f :: (Bool, Int, Int) -> DS.Set (Bool, Int, Int) -> DS.Set (Bool, Int, Int)
--       f (_, y, x)
--         = modify (True, y, x - 1) (False, y, x - 1)
--         . modify (True, y, x + 1) (False, y, x + 1)
--         . modify (True, y - 1, x) (False, y - 1, x)
--         . modify (True, y + 1, x) (False, y + 1, x)

-- e :: (Int, Int, [(Int, Int, Int)]) -> Int
-- e (h, w, areas) = if null free then -1 else result - 1 where
--   result
--     = DS.findMax
--     -- . DT.traceShowId
--     . DS.map (\ (y, x) -> tryOccupy occupyed [(y, x, 0)])
--     $ free
--   matrix = DS.fromList [(True, y, x) | y <- [1..h], x <- [1..w]]
--   matrix' = foldr occupy matrix areas
--   -- free = traceTaged "free" . DS.map f . DS.filter (\ (b, _, _) -> b) $ matrix'
--   free = DS.map f . DS.filter (\ (b, _, _) -> b) $ matrix'
--   -- occupyed = traceTaged "occupyed" . DS.map f . DS.filter (\ (b, _, _) -> not b) $ matrix'
--   occupyed = DS.map f . DS.filter (\ (b, _, _) -> not b) $ matrix'
--   f :: (Bool, Int, Int) -> (Int, Int)
--   f (_, y, x) = (y, x)
--   occupy :: (Int, Int, Int) -> DS.Set (Bool, Int, Int) -> DS.Set (Bool, Int, Int)
--   occupy (_, _, -1) = id
--   occupy (y, x, s)
--       = occupy (y, x - 1, s - 1)
--       . occupy (y, x + 1, s - 1)
--       . occupy (y - 1, x, s - 1)
--       . occupy (y + 1, x, s - 1)
--       . modify (True, y, x) (False, y, x)
--   tryOccupy :: DS.Set (Int, Int) -> [(Int, Int, Int)] -> Int
--   tryOccupy occupyed ((cy, cx, step):rest)
--     | (cy, cx) `DS.member` occupyed = step
--     | otherwise = tryOccupy occupyed $ rest ++
--       [ (cy, cx - 1, step + 1)
--       , (cy, cx + 1, step + 1)
--       , (cy - 1, cx, step + 1)
--       , (cy + 1, cx, step + 1) ]

-- modify :: Ord a => a -> a -> DS.Set a -> DS.Set a
-- modify old new set
--   | old `DS.notMember` set = set -- WARNING: modifying a non-existing element
--   | otherwise = DS.insert new . DS.delete old $ set
