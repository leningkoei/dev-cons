module Main where

main :: IO ()
main = r >>= return . e >>= p

r :: IO Int
r = read <$> getLine

p :: Int -> IO ()
p = print

e :: Int -> Int
e 1 = 1
e 2 = 1
e n = e (n - 1) + e (n - 2)
