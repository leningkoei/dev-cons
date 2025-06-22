-- SOURCE CODE
def Float.toNat
: (n : Float) → n ≥ 0 → Nat
| n, _ => n.floor.toISize.toNatClampNeg

def evaluate (x y a b : Nat) : Except String (Nat × Bool) :=
  let m : Float := x.toFloat - (b.toFloat / a.toFloat) * y.toFloat
  let n : Float := y.toFloat - (a.toFloat / b.toFloat) * x.toFloat
  let playerWin : Bool := if m ≥ 0 then .true else .false
  if playerWin
    then if h : m ≥ 0
      then .ok (m.toNat h, .true)
      else .error s!"The number of survivors (m = {m}) is negative!"
    else if h : n ≥ 0
      then .ok (n.toNat h, .false)
      else .error s!"The number of survivors (n = {n}) is negative!"

namespace Main

def read (stdio : IO.FS.Stream)
: ExceptT String IO (Nat × Nat × Nat × Nat)
:= do
  let (x, y) ←
    match (← stdio.getLine).trim.split (· = ' ') with
    | [x, y] =>
      match x.toNat?, y.toNat? with
      | .some x, .some y => .ok ∘ .pure <| (x, y)
      | _, _ => .error "Your x or y is not a nat!"
    | _ => .error "Your x and y inputed error!"
  let (a, b) ←
    match (← stdio.getLine).trim.split (· = ' ') with
    | [a, b] =>
      match a.toNat?, b.toNat? with
      | .some a, .some b => .ok ∘ .pure <| (a, b)
      | _, _ => .error "Your a or b is not a nat!"
    | _ => .error "Your a and b inputed error!"
  pure (x, y, a, b)

def print (stdout stderr : IO.FS.Stream)
: Except String (Nat × Bool) → IO Unit
| .ok (survivorNumber, playerWin) => do
  if playerWin
    then stdout.putStrLn "Player"
    else stdout.putStrLn "Enemy"
  stdout.putStrLn s!"{survivorNumber}"
| .error msg => stderr.putStrLn msg

end Main

def main : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  let stderr ← IO.getStderr
  let xyab ← Main.read stdin
  let result := xyab >>= (λ (x, y, a, b) ↦ evaluate x y a b)
  Main.print stdout stderr result
  
-- AIGENERATE CODE
import Control.Monad.Trans.Except
import System.IO (Handle, stdin, stdout, stderr, hGetLine, hPutStrLn)
import Data.Char (isSpace)
import Text.Read (readMaybe)
import Data.Int (Int64)
import qualified Data.Fixed as F

import Control.Monad.Except
import Control.Moand.IO.Class

-- 字符串修剪函数
trim :: String -> String
trim = reverse . dropWhile isSpace . reverse . dropWhile isSpace

-- 安全整数转换（处理负数和溢出）
safeFloor :: Double -> Integer
safeFloor x
  | x < 0     = 0  -- 负数时返回0，符合业务逻辑
  | otherwise = truncate x

-- 核心计算逻辑
evaluate :: Integer -> Integer -> Integer -> Integer -> Except String (Integer, Bool)
evaluate x y a b
  | a == 0 || b == 0 = throwError "Division by zero: a and b must be non-zero"
  | m >= 0           = return (safeFloor m, True)
  | n >= 0           = return (safeFloor n, False)
  | otherwise        = throwError $ unlines
      [ "Both survivors are negative!"
      , "Player survivors (m): " ++ show m
      , "Enemy survivors (n): " ++ show n
      ]
  where
    -- 使用高精度计算
    toDouble :: Integer -> Double
    toDouble = fromIntegral
    
    m = toDouble x - (toDouble b / toDouble a) * toDouble y
    n = toDouble y - (toDouble a / toDouble b) * toDouble x

-- 输入读取函数
readInput :: Handle -> ExceptT String IO (Integer, Integer, Integer, Integer)
readInput h = do
  -- 读取第一行 (x, y)
  xyLine <- liftIO $ trim <$> hGetLine h
  let xyParts = words xyLine
  (x, y) <- case xyParts of
    [xStr, yStr] -> do
      x <- maybe (throwError "Your x is not a number!") return $ readMaybe xStr
      y <- maybe (throwError "Your y is not a number!") return $ readMaybe yStr
      return (x, y)
    _ -> throwError "Expected two numbers for x and y"
  
  -- 读取第二行 (a, b)
  abLine <- liftIO $ trim <$> hGetLine h
  let abParts = words abLine
  (a, b) <- case abParts of
    [aStr, bStr] -> do
      a <- maybe (throwError "Your a is not a number!") return $ readMaybe aStr
      b <- maybe (throwError "Your b is not a number!") return $ readMaybe bStr
      return (a, b)
    _ -> throwError "Expected two numbers for a and b"
  
  return (x, y, a, b)

-- 输出结果
printResult :: Handle -> Handle -> Except String (Integer, Bool) -> IO ()
printResult out _ (Right (survivor, True)) = do
  hPutStrLn out "Player"
  hPutStrLn out $ show survivor
printResult out _ (Right (survivor, False)) = do
  hPutStrLn out "Enemy"
  hPutStrLn out $ show survivor
printResult _ err (Left msg) = hPutStrLn err msg

-- 主函数
main :: IO ()
main = do
  inputResult <- runExceptT $ readInput stdin
  case inputResult of
    Left err -> hPutStrLn stderr err
    Right (x, y, a, b) -> do
      let result = evaluate x y a b
      printResult stdout stderr (runExcept result)
