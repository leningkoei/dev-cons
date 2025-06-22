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
