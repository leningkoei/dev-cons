import Control.Monad (forM_, when, unless, forM, foldM)
import Control.Monad.ST (runST, ST)
import Data.Array.ST (STArray, newArray, readArray, writeArray)
import Data.Sequence (Seq(..), (|>))
import qualified Data.Sequence as Seq
import Data.STRef (newSTRef, readSTRef, modifySTRef', writeSTRef)
import Data.Foldable (traverse_)

main :: IO ()
main = do
  (h, w, areas) <- readInput
  let result = evaluate h w areas
  if result == -1
    then print result
    else print $ result - 1
  -- print . (+ (-1)) $ evaluate h w areas

readInput :: IO (Int, Int, [(Int, Int, Int)])
readInput = do
  [h, w, n] <- map read . words <$> getLine
  areas <- mapM (const readArea) [1..n]
  return (h, w, areas)
  where
    readArea = do
      line <- getLine
      let [y, x, s] = map read (words line)
      return (y, x, s)

evaluate :: Int -> Int -> [(Int, Int, Int)] -> Int
evaluate h w areas = runST $ do
  distArr <- newArray ((1,1), (h,w)) (-1) :: ST s (STArray s (Int, Int) Int)
  
  -- Process each gang's area using BFS
  forM_ areas $ \(y, x, s) -> do
    when (s >= 0 && y >= 1 && y <= h && x >= 1 && x <= w) $ do
      let initialQueue = Seq.singleton (y, x, s)
      processGang distArr initialQueue h w
  
  -- Collect initial cells for multi-source BFS
  initialQueue <- collectInitialQueue distArr h w
  -- Perform multi-source BFS and check coverage
  (maxDist, allCovered) <- bfs distArr initialQueue h w
  return $ if allCovered then maxDist else -1

processGang :: STArray s (Int, Int) Int -> Seq (Int, Int, Int) -> Int -> Int -> ST s ()
processGang distArr queue h w = case Seq.viewl queue of
  Seq.EmptyL -> return ()
  (y, x, s) Seq.:< rest -> do
    currentDist <- readArray distArr (y, x)
    if currentDist == 0 || s < 0
      then processGang distArr rest h w
      else do
        writeArray distArr (y, x) 0
        when (s > 0) $ do
          let directions = [(y-1, x), (y+1, x), (y, x-1), (y, x+1)]
          forM_ directions $ \(ny, nx) -> do
            when (ny >= 1 && ny <= h && nx >= 1 && nx <= w) $ do
              processGang distArr (rest |> (ny, nx, s-1)) h w
        --  processGang distArr rest h w

collectInitialQueue :: STArray s (Int, Int) Int -> Int -> Int -> ST s (Seq (Int, Int))
collectInitialQueue distArr h w = do
  let coords = [(y, x) | y <- [1..h], x <- [1..w]]
  foldM (\q (y, x) -> do
    d <- readArray distArr (y, x)
    if d == 0 then return (q |> (y, x)) else return q
    ) Seq.empty coords

bfs :: STArray s (Int, Int) Int -> Seq (Int, Int) -> Int -> Int -> ST s (Int, Bool)
bfs distArr initialQueue h w = do
  maxDistRef <- newSTRef 0
  queueRef <- newSTRef initialQueue
  allCoveredRef <- newSTRef True
  
  let processQueue = do
        currentQueue <- readSTRef queueRef
        unless (Seq.null currentQueue) $ do
          writeSTRef queueRef Seq.empty
          maxDist <- readSTRef maxDistRef
          anyProcessedRef <- newSTRef False
          
          traverse_ (\(y, x) -> do
            let dirs = [(y-1, x), (y+1, x), (y, x-1), (y, x+1)]
            forM_ dirs $ \(ny, nx) -> do
              when (ny >= 1 && ny <= h && nx >= 1 && nx <= w) $ do
                d <- readArray distArr (ny, nx)
                when (d == -1) $ do
                  writeArray distArr (ny, nx) (maxDist + 1)
                  modifySTRef' queueRef (|> (ny, nx))
                  writeSTRef anyProcessedRef True
            ) currentQueue
          
          anyProcessed <- readSTRef anyProcessedRef
          when anyProcessed $ modifySTRef' maxDistRef (+1)
          processQueue
  processQueue
  
  maxDist <- readSTRef maxDistRef
  allCovered <- checkAllCovered distArr h w
  return (maxDist, allCovered)

checkAllCovered :: STArray s (Int, Int) Int -> Int -> Int -> ST s Bool
checkAllCovered arr h w = do
  let coords = [(y, x) | y <- [1..h], x <- [1..w]]
  results <- forM coords $ \(y, x) -> do
    d <- readArray arr (y, x)
    return (d /= -1)
  return (and results)
