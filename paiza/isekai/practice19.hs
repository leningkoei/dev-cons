module Main where

main :: IO ()
main = r >>= return . e >>= p >> return ()

r :: IO Int
r = read <$> getLine

p :: Int -> IO ()
p = print

e :: Int -> Int
e n = length . getGcds $ n where
  getGcds :: Int -> [Int]
  getGcds n
    | n < 2 = []
    | n == 2 = [2]
    | gcd n = n : gcds
    | otherwise = gcds
    where
      gcds = getGcds (n - 1)
      gcd n = null . filter (\ m -> n `mod` m == 0) $ gcds
