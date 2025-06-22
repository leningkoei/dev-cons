module Main where

import Control.Monad qualified as CM
-- import Control.Monad.ST qualified as CMS
import Data.Array.MArray qualified as DAM
import Data.Array.ST qualified as DAS
import Data.Array.IArray qualified as DAI
import Data.Array.Unboxed qualified as DAU

main :: IO ()
main = do
  let result = sum1 3 [1..3]
  print . DAI.elems $ result

sum1 :: Int -> [Int] -> DAU.UArray Int Int
sum1 n xs = DAS.runSTUArray $ do
  arr <- DAM.newArray (0, n) 0
  CM.forM_ (zip [0 .. n - 1] xs) $ \ (i, dx) -> do
    acc <- DAM.readArray arr i
    DAM.writeArray arr (i + 1) $ acc + dx
  return arr
