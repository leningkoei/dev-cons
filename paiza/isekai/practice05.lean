def main : IO Unit := do
  (← IO.getStdout).putStrLn s!"{13 - 10000 % 13 + 10000}"
