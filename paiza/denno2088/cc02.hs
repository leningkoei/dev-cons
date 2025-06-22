--  -7 |  -6 |  -5 | -4 | -3 | -2 | -1 | 0 | 1 |  2 |  3 |  4 |  5  |  6  |  7
-- -----------------------------------------------------------------------------
-- 212 | 210 | 211 | 22 | 20 | 21 |  2 | 0 | 1 | 12 | 10 | 11 | 122 | 120 | 121

module Main where

main :: IO ()
main = p =<< e <$> r

r :: IO Int
r = read <$> getLine

p :: String -> IO ()
p = putStrLn

e' :: Int -> String
e' x
  | x == 0 = ""
  | remainder == 0 = '0' : e' quotient
  | remainder == 1 = '1' : e' quotient
  | remainder == 2 = '2' : e' (quotient + 1)
  where
    remainder = x `mod` 3
    quotient = x `div` 3

minus :: String -> String
minus [] = []
minus (x : xs)
  | x == '0' = '0' : xs'
  | x == '1' = '2' : xs'
  | x == '2' = '1' : xs'
  where
    xs' = minus xs

e :: Int -> String
e x
  | x < 0 = minus ep
  | x > 0 = ep
  | x == 0 = "0"
  where
    ep = reverse . e' . abs $ x
