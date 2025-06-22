module Main where

-- import Control.Monad qualified as CM
-- import Data.Array.IArray qualified as DAI
import qualified Control.Monad as CM
import qualified Data.Array.IArray as DAI
import Data.Array.IArray ((!))

main :: IO ()
main = CM.void $ r >>= return . e >>= p

r :: IO [Int]
r = do
  _n <- getLine
  as <- map read . words <$> getLine
  return as

p :: [[Int]] -> IO [()]
p =  mapM (putStrLn . unwords. map show)

e :: [Int] -> [[Int]]
e as = result where
  as' :: DAI.Array Int Int
  as' = DAI.listArray (0, length as - 1) as
  result = map f [0..length as - 1]
  f :: Int -> [Int]
  f i = map (\ j -> as' ! i * as' ! j) [0..length as - 1]
