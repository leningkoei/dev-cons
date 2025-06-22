-- source code:
-- namespace Main
-- 
-- def List.fromRange
-- : (first : Nat) → (last : Nat) → List Nat
-- | first, last => helper (last - first) first
-- where
--   helper : Nat → Nat → List Nat
--   | 0, last => [last]
--   | n + 1, current => current :: helper n (current + 1)
-- 
-- def read (stdin : IO.FS.Stream) : IO Nat := do
--   let n? ← (λ s ↦ s.trim.toNat?) <$> stdin.getLine
--   match n? with
--   | .some n => pure n
--   | _ => panic! "Given `n` is not a number!"
-- 
-- def evaluate
-- : Nat → Bool
-- | 0 | 1 | 2 => panic! "Given `n` is less than 3!"
-- | n => List.fromRange 1 (n - 2) |>.any (enumA n)
-- where
--   enumA (n a : Nat) : Bool := List.fromRange 1 (n - a - 1) |>.any (enumB n a)
--   enumB (n a b : Nat) : Bool :=
--     let c := n - a - b
--     if a < b ∧ b < c then a^2 + b^2 = c^2 else .false
-- 
-- def print (stdout : IO.FS.Stream) : Bool → IO Unit
-- | .true => stdout.putStrLn "YES"
-- | .false => stdout.putStrLn "NO"
-- 
-- def main : IO Unit := do
--   print (← IO.getStdout) ∘ evaluate =<< read (← IO.getStdin)
-- 
-- end Main
-- 
-- def main : IO Unit := Main.main

-- ai generated code:
import System.IO (Handle, stdin, stdout, hGetLine, hPutStrLn)
import Data.Char (isSpace)
import Text.Read (readMaybe)

-- 生成从 first 到 last 的连续整数列表
fromRange :: Int -> Int -> [Int]
fromRange first last = helper (last - first) first
  where
    helper 0 current = [current]
    helper steps current = current : helper (steps - 1) (current + 1)

-- 读取输入数字
readInput :: Handle -> IO Int
readInput h = do
  line <- trim <$> hGetLine h
  case readMaybe line of
    Just n -> return n
    _ -> error "Given `n` is not a number!"
  where
    trim = reverse . dropWhile isSpace . reverse . dropWhile isSpace

-- 检查是否存在满足勾股定理的三个正整数
evaluate :: Int -> Bool
evaluate n
  | n < 3     = error "Given `n` is less than 3!"
  | otherwise = any (enumA n) (fromRange 1 (n - 2))
  where
    enumA n a = any (enumB n a) (fromRange 1 (n - a - 1))
    enumB n a b = 
      let c = n - a - b
      in a < b && b < c && a^2 + b^2 == c^2

-- 输出结果
printResult :: Handle -> Bool -> IO ()
printResult h True  = hPutStrLn h "YES"
printResult h False = hPutStrLn h "NO"

-- 主函数
main :: IO ()
main = do
  n <- readInput stdin
  printResult stdout (evaluate n)
