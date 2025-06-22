import Control.Monad.Trans.Reader (ReaderT, runReaderT, ask)
import Control.Monad.Trans.State (StateT, runStateT, get, put)
import Control.Monad.IO.Class (liftIO)
import System.IO (Handle, stdin, stdout, hGetLine, hPutStrLn)
import Data.List (sort, elemIndex)
import Data.Char (isSpace)
import Text.Read (readMaybe)

import Control.Monad
import Control.Monad.Trans

-- 列表生成函数
generate :: a -> Int -> [a]
generate _ 0 = []
generate elem len = elem : generate elem (len - 1)

-- 环境数据结构
data Env = Env
  { stdinHandle :: Handle
  , stdoutHandle :: Handle
  , pVal :: Int
  }

-- 状态数据结构 (仅存储索引)
data Sta = Sta
  { currentIndex :: Int
  }

-- 事件类型
data Event = Join Int | Sorting
  deriving Show

-- 字符串修剪函数
trim :: String -> String
trim = f . f
  where
    f = reverse . dropWhile isSpace

-- 输入读取函数
readInput :: Handle -> IO (Int, Int, [Int])
readInput h = do
  line <- trim <$> hGetLine h
  let nkp = words line
  (n, k, p) <- case nkp of
    [nStr, kStr, pStr] ->
      case (readMaybe nStr, readMaybe kStr, readMaybe pStr) of
        (Just n, Just k, Just p) -> return (n, k, p)
        _ -> fail "nkp is not a nat!"
    _ -> if length nkp < 3
         then fail "nkp is not enough!"
         else fail "nkp is too much"
  
  lines <- replicateM n (trim <$> hGetLine h)
  ps <- forM lines $ \s ->
    case readMaybe s of
      Just n -> return n
      _ -> fail "someone's height is not a nat!"
  
  return (k, p, p : ps)

-- 事件处理函数 (仅维护索引)
runEvent :: Int -> StateT Sta (ReaderT Env IO) ()
runEvent k
  | k <= 0 = return ()
  | otherwise = do
      env <- lift ask
      line <- liftIO $ trim <$> hGetLine (stdinHandle env)
      let tokens = words line
      
      event <- case tokens of
        ["join", pStr] ->
          case readMaybe pStr of
            Just p' -> return $ Join p'
            _ -> liftIO $ fail "join event received is not a nat!"
        ["sorting"] -> return Sorting
        _ -> liftIO $ fail "event not satisfied!"
      
      case event of
        Join p' -> do
          if p' < pVal env
            then do
              currentIndex <- currentIndex <$> get
              put $ Sta (currentIndex + 1)
            else if p' > pVal env
              then return ()
              else liftIO $ fail "your height of the insert classmate is same as Mr.paiza's!"
          runEvent (k - 1)
        
        Sorting -> do
          idx <- currentIndex <$> get
          liftIO $ hPutStrLn (stdoutHandle env) (show (idx + 1))
          runEvent (k - 1)

-- 主函数
main :: IO ()
main = do
  (k, p, ps) <- readInput stdin
  -- 计算初始索引
  let sortedPs = sort ps
  initialIndex <- case elemIndex p sortedPs of
    Just idx -> return idx
    Nothing -> fail "your class does not have Mr.paiza"
  
  let env = Env stdin stdout p
  let sta = Sta initialIndex
  runReaderT (runStateT (runEvent k) sta) env
  return ()
  