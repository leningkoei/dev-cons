module Main where

main :: IO ()
main = p =<< e <$> r

r :: IO (Int, Int, Int)
r = do
  a <- read <$> getLine
  b <- read <$> getLine
  c <- read <$> getLine
  return (a, b, c)

p :: Int -> IO ()
p = print

e :: (Int, Int, Int) -> Int
e (a, b, c) = 1 * a + 5 * b + 10 * c
