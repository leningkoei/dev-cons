namespace Main

def List.fromRange
: (first : Nat) → (last : Nat) → List Nat
| first, last => helper (last - first) first
where
  helper : Nat → Nat → List Nat
  | 0, last => [last]
  | n + 1, current => current :: helper n (current + 1)

def read (stdin : IO.FS.Stream) : IO Nat := do
  let n? ← (λ s ↦ s.trim.toNat?) <$> stdin.getLine
  match n? with
  | .some n => pure n
  | _ => panic! "Given `n` is not a number!"

def evaluate
: Nat → Bool
| 0 | 1 | 2 => panic! "Given `n` is less than 3!"
| n => List.fromRange 1 (n - 2) |>.any (enumA n)
where
  enumA (n a : Nat) : Bool := List.fromRange 1 (n - a - 1) |>.any (enumB n a)
  enumB (n a b : Nat) : Bool :=
    let c := n - a - b
    if a < b ∧ b < c then a^2 + b^2 = c^2 else .false

def print (stdout : IO.FS.Stream) : Bool → IO Unit
| .true => stdout.putStrLn "YES"
| .false => stdout.putStrLn "NO"

def main : IO Unit := do
  print (← IO.getStdout) ∘ evaluate =<< read (← IO.getStdin)

end Main

def main : IO Unit := Main.main

example : 37 * x + q = 37 * x + q := by rfl

example (h : y = (x + 7)) : 2 * y = 2 * (x + 7) := by rw[h]

example : 2 = .succ (.succ 0) := by
  -- rw[two_eq_succ_one]
  rfl
-- where
--   two_eq_succ_one : 2 = .succ 1 := by
--     rfl

namespace NNG4

inductive ℕ : Type where
| zero : ℕ
| succ : ℕ → ℕ

def I : ℕ := .succ .zero
def II : ℕ := .succ I
def III : ℕ := .succ II
def IV : ℕ := .succ III

theorem two_eq_succ_one : II = .succ I := by rfl
theorem one_eq_succ_zero : I = .succ .zero := by rfl

example : II = .succ (.succ .zero) := by
  rw[two_eq_succ_one]
  rw[one_eq_succ_zero]

end NNG4
