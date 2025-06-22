module Main where

main :: IO ()
main = pure [1..100] >>= pure . e >>= p >> pure ()

e :: [Int] -> [String]
e [] = []
e (n : ns) = n' : e ns where
  fizz = n `mod` 3 == 0
  buzz = n `mod` 5 == 0
  n'| fizz && buzz = "FizzBuzz"
    | fizz = "Fizz"
    | buzz = "Buzz"
    | otherwise = show n

p :: [String] -> IO [()]
p = mapM putStrLn
