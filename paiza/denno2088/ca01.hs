module Main where

-- import Debug.Trace qualified as DT

-- import Data.List qualified as DL
import qualified Data.List as DL
-- import Data.Set qualified as DS
import qualified Data.Set as DS

main :: IO ()
main = p =<< e <$> r

--        ay   ax     by   bx    map
r :: IO ((Int, Int), (Int, Int), DS.Set (Bool, Int, Int))
r = do
  [h, _] <- map read . words <$> getLine
  matrix <- loop h
  let matrix' = concat . bindyx $ matrix
  let a = locate 'A' matrix'
  let b = locate 'B' matrix'
  let matrix'' = map replaceRule matrix'
  return (a, b, DS.fromList matrix'')
  where
    loop :: Int -> IO [[Char]]
    loop 0 = return []
    loop h = do
      line <- getLine
      lines <- loop (h - 1)
      return (line : lines)
    locate :: Char -> [(Char, Int, Int)] -> (Int, Int)
    locate char matrix = case DL.find (\ (c, _, _) -> c == char) matrix of
      Just (_, y, x) -> (y, x)
      Nothing -> undefined
    replaceRule :: (Char, a, b) -> (Bool, a, b)
    replaceRule ('A', y, x) = (True, y, x)
    replaceRule ('B', y, x) = (True, y, x)
    replaceRule ('.', y, x) = (True, y, x)
    replaceRule ('#', y, x) = (False, y, x)

bindyx :: [[a]] -> [[(a, Int, Int)]]
bindyx matrix = loop 0 matrix' where
  matrix' = map (zip [0..]) matrix
  loop :: Int -> [[(Int, a)]] -> [[(a, Int, Int)]]
  loop _ [] = []
  loop y (line:lines) = map (\ (x, a) -> (a, y, x)) line : loop (y + 1) lines

p :: Int -> IO ()
p = print

e :: ((Int, Int), (Int, Int), DS.Set (Bool, Int, Int)) -> Int
e (a@(ay, ax), b, matrix) = memoedBFS initMemo initQueue b matrix where
  initMemo = DS.fromList [a]
  initQueue = [(ay, ax, 0)]
  memoedBFS
    :: DS.Set (Int, Int)
    -> [(Int, Int, Int)]
    -> (Int, Int)
    -> DS.Set (Bool, Int, Int)
    -> Int
  memoedBFS _ [] _ _ = -1
  memoedBFS memo ((cy, cx, step):rest) target@(ty, tx) map
    | findable (cy, cx) target = step
    | otherwise = memoedBFS memo' queue' target map
    where
      left = (cy, cx - 1)
      right = (cy, cx + 1)
      up = (cy - 1, cx)
      down = (cy + 1, cx)
      go
        :: (Int, Int)
        -> (DS.Set (Int, Int), [(Int, Int, Int)])
        -> (DS.Set (Int, Int), [(Int, Int, Int)])
      go direct@(y, x) (memo, queue) =
        if (True, y, x) `DS.member` map
        && not (direct `DS.member` memo)
          then (direct `DS.insert` memo, queue ++ [(y, x, step + 1)])
          else (memo, queue)
      (memo', queue') = go left . go right . go up . go down $ (memo, rest)
      findable :: (Int, Int) -> (Int, Int) -> Bool
      findable (cy, cx) (ty, tx)
        | cy == ty = null
          -- . DT.traceShowId
          . DS.filter (\ (transparent, _, _) -> not transparent)      -- walls
          . DS.filter (\ (_, _, x) -> x > min cx tx && x < max cx tx) -- range
          . DS.filter (\ (_, y, _) -> y == cy)                        -- line
          $ map
        | cx == tx = null
          -- . DT.traceShowId
          . DS.filter (\ (transparent, _, _) -> not transparent)      -- walls
          . DS.filter (\ (_, y, _) -> y > min cy ty && y < max cy ty) -- range
          . DS.filter (\ (_, _, x) -> x == cx)                        -- line
          $ map
        | otherwise = False
