inductive Expect (ε : Type) (α : Type) : Type where
| error : ε → Expect ε α
| ok : α → Expect ε α

instance : Monad (Expect ε) where
  pure := Expect.ok
  bind result next :=
    match result with
    | Expect.error msg => Expect.error msg
    | Expect.ok x => next x
