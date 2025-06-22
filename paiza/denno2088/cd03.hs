module Main where

main :: IO ()
main = p =<< e <$> r

r :: IO Int
r = do
  n <- read <$> getLine
  return n

p :: Int -> IO ()
p = print

e :: Int -> Int
e n = n `div` 2 + 100
