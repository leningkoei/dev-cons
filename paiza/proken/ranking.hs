module Main where

-- import Data.List qualified as DL
import qualified Data.List as DL

main :: IO ()
main = r >>= return . e >>= p

r :: IO [String]
r = mapM (const getLine) [1..5]

p :: Char -> IO ()
p x = putStrLn (x : [])

e :: [String] -> Char
e matrix = if null result then 'D' else head result where
  test :: String -> Char
  test list = foldr (\ c head -> if c == head then head else '.') (head list) list
  rows = map test matrix
  cols = map test . DL.transpose $ matrix
  diagonal1 = test . diagonal $ matrix
  diagonal2 = test . diagonal . map reverse $ matrix
  result = filter (/= '.') $ diagonal1 : diagonal2 : rows ++ cols

diagonal :: [[a]] -> [a]
diagonal xs = zipWith (!!) xs [0..]
