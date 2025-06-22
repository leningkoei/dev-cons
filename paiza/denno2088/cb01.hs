module Main where

-- import Data.Set qualified as DS
import qualified Data.Set as DS
-- import Debug.Trace qualified as DT

main :: IO ()
main = p =<< e <$> r

r :: IO (DS.Set (Int, Int))
r = do
  n <- read <$> getLine
  DS.fromList . concat <$> (loop n 1)
  where
    loop :: Int -> Int -> IO [[(Int, Int)]]
    loop 0 _ = return []
    loop n y = do
      line <- map f . zip [1..] <$> getLine
      let line' = map (\ (_, y, x) -> (y, x)) . filter (\ (v, _, _) -> v) $ line
      lines <- loop (n - 1) (y + 1)
      return (line' : lines)
      where
        f :: (Int, Char) -> (Bool, Int, Int)
        f (x, '.') = (True, y, x)
        f (x, '#') = (False, y, x)

p :: Int -> IO ()
p = print

e :: DS.Set (Int, Int) -> Int
e matrix = foldr f 0 matrix where
  f o counter = counter + (length .
    -- DT.traceShowId .
    DS.filter (findC matrix o) .
    DS.filter (findB matrix o) $
    (as matrix o))
  as :: DS.Set (Int, Int) -> (Int, Int) -> DS.Set (Int, Int)
  as matrix (oy, ox) = DS.filter (\ (ay, ax) -> ay == oy && ax > ox) matrix
  findB :: DS.Set (Int, Int) -> (Int, Int) -> (Int, Int) -> Bool
  findB matrix (oy, ox) (ay, ax) = (oy + (ax - ox), ox) `DS.member` matrix
  findC :: DS.Set (Int, Int) -> (Int, Int) -> (Int, Int) -> Bool
  findC matrix (oy, ox) (ay, ax) = (oy + (ax - ox), ax) `DS.member` matrix
