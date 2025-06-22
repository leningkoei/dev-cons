module Main where

main :: IO ()
main = do
  p . e =<< r
  pure ()

r :: IO (Matrix Int)
r = do
  [n, _k] <- map read . words <$> getLine
  sequence [map read . words <$> getLine | _ <- [1..n]]

p :: Matrix Int -> IO [()]
p = mapM (putStrLn . unwords . map show)

e :: Matrix Int -> Matrix Int
e = transpose

type Matrix a = [[a]]

transpose :: Matrix a -> Matrix a
transpose matrix = result where
  k = length . head $ matrix
  n = length matrix
  result = [[matrix !! y !! x | y <- [0..n - 1]] | x <- [0..k - 1]]
