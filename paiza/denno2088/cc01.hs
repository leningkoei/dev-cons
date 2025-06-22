module Main where

import Data.Set qualified as DS

main :: IO ()
main = p =<< e <$> r

r :: IO String
r = do
  _ <- getLine
  getLine

p :: Int -> IO ()
p = print

e :: String -> Int
e cookies = DS.size cookiesSet
  where
    cookiesSet = DS.fromList cookies
