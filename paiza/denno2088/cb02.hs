module Main where

main :: IO ()
main = p =<< e <$> r

r :: IO [[Bool]]
r = do
  n <- read <$> getLine
  loop n
  where
    loop :: Int -> IO [[Bool]]
    loop 0 = return []
    loop n = do
      line <- words <$> getLine
      let line' = map f line
      lines <- loop (n - 1)
      return (line' : lines)
    f :: String -> Bool
    f "0" = False
    f "1" = True

p :: Bool -> IO ()
p False = putStrLn "No"
p True = putStrLn "Yes"

e :: [[Bool]] -> Bool
e matrix = matrix == matrix' where
  matrix' = map reverse matrix
