module Main where

import qualified Control.Monad as CM

main :: IO ()
main = CM.void $ return e >>= p

p :: [String] -> IO [()]
p = mapM putStrLn

e :: [String]
e = result where
  minutes = [(h, m) | h <- [0..23], m <- [0..59]]
  result = map f minutes
  f (h, m) = ""
    ++ (if (h + m) `mod` 3 == 0 then "FIZZ" else "")
    ++ (if (h + m) `mod` 5 == 0 then "BUZZ" else "")
