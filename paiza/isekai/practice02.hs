module Main where

import qualified Control.Monad as CM

main :: IO ()
main = CM.void $ return e >>= p

p :: Int -> IO ()
p = print

e :: Int
e = result where
  result = maximum
    [ x * y
    | x <- [1..99]
    , y <- [1..99]
    , x + 1 < 100
    , x ^ 3 + y ^ 3 < 100000 ]
