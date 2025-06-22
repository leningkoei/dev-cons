module Main where

import qualified Control.Monad as CM

main :: IO ()
main = CM.void $ r >>= return . e' >>= p

r :: IO (Int, Int, Int)
r = do
  [x, y, z] <- map read . words <$> getLine
  return (x, y, z)
  -- When you use ERROR method...
  -- let x' = min x y
  -- let y' = max x y
  -- return (x', y', z)

p :: Int -> IO ()
p = print

-- -- ERROR
-- e :: (Int, Int, Int) -> Int
-- e (x, y, z) = qy + qx + q1 where
--   qy = z `div` y
--   ry = z `mod` y
--   qx = ry `div` x
--   rx = ry `mod` x
--   q1 = rx

e :: (Int, Int, Int) -> Int
e (x, y, z) = result where
  max1 = z
  cxMax = z `div` x
  cyMax = z `div` y
  result = minimum
    [ cx + cy + c1
    | cx <- [0..cxMax]
    , cy <- [0..cyMax]
    , let c1 = z - cx * x - cy * y
    , c1 >= 0 ]

e' :: (Int, Int, Int) -> Int
e' (x, y, z) = result where
  matrix = map f [0..z `div` x]
  f :: Int -> [Int]
  f cx = map (\ cy -> z - cx * x - cy * y + cx + cy) [0..(z - cx * x) `div` y]
  result = minimum . concat $ matrix
