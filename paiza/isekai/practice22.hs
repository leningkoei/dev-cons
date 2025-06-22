module Main where

-- import Data.Array.IArray qualified as DAI
import qualified Data.Array.IArray as DAI
import Data.Array.IArray ((!))

main :: IO ()
main = do
  p . e =<< r
  pure ()

r :: IO ([Int], [Int])
r = do
  [n, k] <- map read . words <$> getLine
  as <- mapM (const (read <$> getLine)) [1..n]
  qs <- mapM (const (read <$> getLine)) [1..k]
  return (as, qs)

p :: [Int] -> IO [()]
p = mapM print

e :: ([Int], [Int]) -> [Int]
e (as, qs) = result where
  as' = 0 : zipWith (+) as as'
  as'' :: DAI.Array Int Int
  as'' = DAI.listArray (0, length as') as'
  result = map f qs
  f :: Int -> Int
  -- f i = sum . take i $ as
  f i = as'' ! i
