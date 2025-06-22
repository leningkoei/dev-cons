module Main where

main :: IO ()
main = p =<< e <$> r

r :: IO [Int]
r = do
  n <- read <$> getLine
  loop n
  where
    loop :: Int -> IO [Int]
    loop 0 = return []
    loop n = do
      x <- read <$> getLine
      xs <- loop (n - 1)
      return (x : xs)

p :: Int -> IO ()
p = print

e :: [Int] -> Int
e = maximum
