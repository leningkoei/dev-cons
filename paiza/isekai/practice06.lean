structure Env : Type where
  n : Nat
  a : Nat
  b : Nat
structure Ctx : Type where
  paiza : Nat
  kiri : Nat
  isPaizaTurn : Bool

partial def evaluate
: StateT Ctx (ReaderT Env Id) Nat
:= do
  let env ← read
  if (← get).kiri > env.n then return 0
  if (← get).isPaizaTurn
    then
      set {(← get) with
        kiri := (← get).paiza * env.a + (← get).kiri,
        isPaizaTurn := .false,
      }
      (· + 1) <$> evaluate
    else
      set {(← get) with
        paiza := (← get).kiri % env.b + (← get).paiza,
        isPaizaTurn := .true,
      }
      evaluate

partial def evaluate' (n a b paiza kiri : Nat) (isPaizaTurn : Bool) : Nat :=
  if kiri > n
    then 0
    else if isPaizaTurn
      then
        1 + evaluate' n a b paiza (paiza * a + kiri) .false
      else
        evaluate' n a b (kiri % b + paiza) kiri .true

namespace Main

def read (stdin : IO.FS.Stream)
: ExceptT String IO (Nat × Nat × Nat)
:= do
  let n? ← (λ s ↦ s.trim.toNat?) <$> stdin.getLine
  let n ←
    match n? with
    | .some n => .ok (.pure n)
    | _ => .error "Your n is not a number!"
  let ab ← (λ s ↦ s.trim.split (· == ' ')) <$> stdin.getLine
  let (a?, b?) ←
    match ab with
    | [a, b] => .ok (.pure (a.toNat?, b.toNat?))
    | _ => .error "Your number of a b is not 2!"
  let (a, b) ←
      match a?, b? with
      | .some a, .some b => .ok (.pure (a, b))
      | _, _ => .error "Your a b are not two number!"
  pure (n, a, b)

def print (stdout : IO.FS.Stream)
: Nat → IO Unit
| n => stdout.putStrLn s!"{n}"

end Main

def main : IO Unit := do
  let stdio ← IO.getStdin
  let stdout ← IO.getStdout
  let nab? ← Main.read stdio
  match nab? with
  | .ok (n, a, b) =>
    -- let env : Env := ⟨n, a, b⟩
    -- let ctx : Ctx := ⟨1, 1, .true⟩
    -- let result := evaluate |>.run' ctx |>.run env |>.run
    let result := evaluate' n a b 1 1 .true
    Main.print stdout result
  | .error msg => stdout.putStrLn msg
