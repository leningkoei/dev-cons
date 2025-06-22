module Main where

-- import Data.List qualified as DL
-- import Data.Ord qualified as DO
import qualified Data.List as DL
import qualified Data.Ord as DO

main :: IO ()
main = p =<< e <$> r

r :: IO ((Int, Int), [(Int, Int, Int)])
r = do
  [n, y, x] <- map read . words <$> getLine
  piicons <- loop n 1
  return ((y, x), piicons)
  where
    loop :: Int -> Int -> IO [(Int, Int, Int)]
    loop 0 _ = return []
    loop remainder counter = do
      [y, x] <- map read . words <$> getLine
      piicons <- loop (remainder - 1) (counter + 1)
      return ((counter, y, x) : piicons)

p :: Int -> IO ()
p = print

e :: ((Int, Int), [(Int, Int, Int)]) -> Int
e ((y, x), piicons) = fst shortestPiicon where
  piicons' = map f piicons
  f (index, y', x') = (index, (y' - y)^2 + (x' - x)^2)
  shortestPiicon = DL.minimumBy (DO.comparing snd) piicons'
