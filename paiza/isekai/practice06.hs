-- SOURCE CODE
-- structure Env : Type where
--   n : Nat
--   a : Nat
--   b : Nat
-- structure Ctx : Type where
--   paiza : Nat
--   kiri : Nat
--   isPaizaTurn : Bool
-- 
-- partial def evaluate
-- : StateT Ctx (ReaderT Env Id) Nat
-- := do
--   let env ← read
--   if (← get).kiri > env.n then return 0
--   if (← get).isPaizaTurn
--     then
--       set {(← get) with
--         kiri := (← get).paiza * env.a + (← get).kiri,
--         isPaizaTurn := .false,
--       }
--       (· + 1) <$> evaluate
--     else
--       set {(← get) with
--         paiza := (← get).kiri % env.b + (← get).paiza,
--         isPaizaTurn := .true,
--       }
--       evaluate
-- 
-- partial def evaluate' (n a b paiza kiri : Nat) (isPaizaTurn : Bool) : Nat :=
--   if kiri > n
--     then 0
--     else if isPaizaTurn
--       then
--         1 + evaluate' n a b paiza (paiza * a + kiri) .false
--       else
--         evaluate' n a b (kiri % b + paiza) kiri .true
-- 
-- namespace Main
-- 
-- def read (stdin : IO.FS.Stream)
-- : ExceptT String IO (Nat × Nat × Nat)
-- := do
--   let n? ← (λ s ↦ s.trim.toNat?) <$> stdin.getLine
--   let n ←
--     match n? with
--     | .some n => .ok (.pure n)
--     | _ => .error "Your n is not a number!"
--   let ab ← (λ s ↦ s.trim.split (· == ' ')) <$> stdin.getLine
--   let (a?, b?) ←
--     match ab with
--     | [a, b] => .ok (.pure (a.toNat?, b.toNat?))
--     | _ => .error "Your number of a b is not 2!"
--   let (a, b) ←
--       match a?, b? with
--       | .some a, .some b => .ok (.pure (a, b))
--       | _, _ => .error "Your a b are not two number!"
--   pure (n, a, b)
-- 
-- def print (stdout : IO.FS.Stream)
-- : Nat → IO Unit
-- | n => stdout.putStrLn s!"{n}"
-- 
-- end Main
-- 
-- def main : IO Unit := do
--   let stdio ← IO.getStdin
--   let stdout ← IO.getStdout
--   let nab? ← Main.read stdio
--   match nab? with
--   | .ok (n, a, b) =>
--     -- let env : Env := ⟨n, a, b⟩
--     -- let ctx : Ctx := ⟨1, 1, .true⟩
--     -- let result := evaluate |>.run' ctx |>.run env |>.run
--     let result := evaluate' n a b 1 1 .true
--     Main.print stdout result
--   | .error msg => stdout.putStrLn msg
--   
-- AIGENERATED CODE
import Control.Monad.Trans.Except
import System.IO (Handle, stdin, stdout, hGetLine, hPutStrLn)
import Data.Char (isSpace)
import Text.Read (readMaybe)

import Control.Monad.IO.Class
import Control.Monad.Except

-- 纯函数版本的评估逻辑
evaluate' :: Integer -> Integer -> Integer -> Integer -> Integer -> Bool -> Integer
evaluate' n a b paiza kiri isPaizaTurn
  | kiri > n = 0
  | isPaizaTurn = 
      1 + evaluate' n a b paiza (paiza * a + kiri) False
  | otherwise = 
      evaluate' n a b (kiri `mod` b + paiza) kiri True

-- 字符串修剪函数
trim :: String -> String
trim = reverse . dropWhile isSpace . reverse . dropWhile isSpace

-- 输入读取函数
readInput :: Handle -> IO (Either String (Integer, Integer, Integer))
readInput h = runExceptT $ do
  nLine <- liftIO $ trim <$> hGetLine h
  n <- case readMaybe nLine of
    Just n -> return n
    Nothing -> throwError "Your n is not a number!"
  
  abLine <- liftIO $ trim <$> hGetLine h
  let abParts = words abLine
  case abParts of
    [aStr, bStr] -> do
      a <- case readMaybe aStr of
        Just a -> return a
        _ -> throwError "Your a is not a number!"
      b <- case readMaybe bStr of
        Just b -> return b
        _ -> throwError "Your b is not a number!"
      return (n, a, b)
    _ -> throwError "Your number of a b is not 2!"

-- 主函数
main :: IO ()
main = do
  inputResult <- readInput stdin
  case inputResult of
    Left err -> hPutStrLn stdout err
    Right (n, a, b) -> do
      let result = evaluate' n a b 1 1 True
      hPutStrLn stdout $ show result

-- PREVIOUS ANSWER
-- module Main where
-- 
-- -- import Debug.Trace qualified as DT
-- 
-- import qualified Control.Monad as CM
-- 
-- main :: IO ()
-- main = CM.void $ r >>= return . e >>= p
-- 
-- r :: IO (Int, Int, Int)
-- r = do
--   n <- read <$> getLine
--   [a, b] <- map read . words <$> getLine
--   return (n, a, b)
-- 
-- p :: Int -> IO ()
-- p = print
-- 
-- -- e :: (Int, Int, Int) -> Int
-- -- e (n, a, b) = f 1 1 where
-- --   f x y
-- --     | y > n = 0
-- --     | otherwise = 1 + f x' y'
-- --     where
-- --       y' = a * x + y
-- --       x' = y' `mod` b + x
-- 
-- e :: (Int, Int, Int) -> Int
-- e (n, a, b) = f 1 1 True where
--   f x y paiza
--     | y > n = 0
--     | paiza = 1 + f x y' False
--     | otherwise = f x' y True
--     where
--       y' = a * x + y
--       x' = y `mod` b + x
