def range100to1 : List Nat :=
  let rec helper : Nat → List Nat
  | 0 => []
  | n + 1 => (n + 1) :: helper n
  helper 100
#eval range100to1.reverse

def eval : List Nat → List String
| [] => []
| n :: rest =>
  let fizz := n % 3
  let buzz := n % 5
  let current :=
    match fizz, buzz with
    | 0, 0 => "FizzBuzz"
    | 0, _ => "Fizz"
    | _, 0 => "Buzz"
    | _, _ => toString n
  current :: eval rest

def print : List String → IO (List Unit) := List.mapM IO.println

def main : IO Unit := do
  let _ ← pure range100to1.reverse >>= pure ∘ eval >>= print
  pure ()
