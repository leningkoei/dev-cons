import Std.Data.HashMap

def List.generate (a : α) : (len : Nat) → List α
| 0 => []
| len + 1 => a :: List.generate a len

namespace Main

def read (stdin : IO.FS.Stream)
: IO (List (Nat × Nat) × List (Nat × Nat)) := do
  let pqr ← (λ s ↦ s.trim.split (· = ' ') |>.map (·.toNat?)) <$> stdin.getLine
  let (p, q, _r) :=
    match pqr with
    | [.some p, .some q, .some r] => (p, q, r)
    | _ => panic! "PQR inputs error!"
  let i2js ← readNatPairs p "Someone of ij pair inputs error!"
  let j2ks ← readNatPairs q "Someone of jk pair inputs error!"
  pure (i2js, j2ks)
where
  readNatPairs : Nat → String → IO (List (Nat × Nat))
  | count, msg => List.map (λ ij ↦
    match ij with
    | [Option.some i, .some j] => (i, j)
    | _ => panic! msg)
    <$> List.map (λ s ↦ s.trim.split (· = ' ') |>.map (·.toNat?))
    <$> (List.generate 0 count |>.mapM (λ _ ↦ stdin.getLine))

def evaluate
: List (Nat × Nat) → StateT (Std.HashMap Nat Nat) Id (List (Nat × Nat))
| [] => pure []
| (i, j) :: i2js => do
  let k? := (← get).get? j
  match k? with
  | .some k => pure <| (i, k) :: (← evaluate i2js)
  | _ => panic! "Exist at least one i do not have any k to help him working!"

def print (stdout : IO.FS.Stream)
: List (Nat × Nat) → IO Unit
| [] => pure ()
| (i, k) :: i2ks => do
  stdout.putStrLn s!"{i} {k}"
  print stdout i2ks

def main : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout

  let (i2js, j2ks) ← read stdin
  let i2ks := evaluate i2js |>.run' (Std.HashMap.ofList j2ks) |>.run
  let i2ks := i2ks.mergeSort
    (λ i₁ i₂ ↦ i₁.1 < i₂.1 ∨ (i₁.1 = i₂.1 ∧ i₁.2 ≤ i₂.2))
  print stdout i2ks

end Main

def main := Main.main
