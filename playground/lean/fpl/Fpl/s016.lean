/-
Write a function to find the last entry in a list. It should return an Option.
-/

def List.last? (list : List α) : Option α :=
  match list with
  | [] => Option.none
  | last :: [] => Option.some last
  | _head :: tail => tail.last?

#eval [1, 2, 3, 4].last?
#eval ([] : List Nat).last?

/-
Write a function that finds the first entry in a list that satisfies a given
predicate. Start the definition with
`def List.findFirst? {α : Type} (xs : List α) (predicate : α → Bool) : Option α :=`.
-/

def List.findFirst? (xs : List α) (predicate : α → Bool) : Option α :=
  match xs with
  | [] => Option.none
  | x :: xs => if predicate x
    then Option.some x
    else xs.findFirst? predicate

/-
Write a function `Prod.swap` that swaps the two fields in a pair. Start the
definition with `def Prod.swap {α β : Type} (pair : α × β) : β × α :=`.
-/

def Prod.swap' (pair : α × β) : β × α :=
  (pair.snd, pair.fst)

/-
Rewrite the `PetName` example to use a custom datatype and compare it to the
version that uses `Sum`.
-/

namespace Origin

def PetName : Type := String ⊕ String

def pets : List PetName := [ Sum.inl "Spot", Sum.inr "Tiger", Sum.inl "Fifi",
  Sum.inl "Rex", Sum.inr "Floof" ]

def howManyDogs (pets : List PetName) : Nat :=
  match pets with
  | [] => 0
  | Sum.inl _ :: morePets => howManyDogs morePets + 1
  | Sum.inr _ :: morePets => howManyDogs morePets

#eval howManyDogs pets

end Origin

inductive PetName : Type where
  | dog : String → PetName
  | cat : String → PetName

def pets : List PetName := [ PetName.dog "Spot", PetName.cat "Tiger",
  PetName.dog "Fifi", PetName.dog "Rex", PetName.cat "Floof" ]

def howManyDogs (pets : List PetName) : Nat :=
  match pets with
  | [] => 0
  | PetName.dog _ :: rest => howManyDogs rest + 1
  | PetName.cat _ :: rest => howManyDogs rest

#eval howManyDogs pets

/-
Write a function `zip` that combines two lists into a list of pairs. The
resulting list should be as long as the shortest input list. Start the
definition with
`def zip {α β : Type} (xs : List α) (ys : List β) : List (α × β) :=`.
-/

def zip (xs : List α) (ys : List β) : List (α × β) :=
  match xs, ys with
  | [], _ => []
  | _, [] => []
  | x :: xs, y :: ys => (x, y) :: zip xs ys

def zipped := zip [1, 2, 3, 4, 5] ['a', 'b', 'c']

#eval zipped

/-
Write a polymorphic function `take` that returns the first `n` entries in a
list, where `n` is a `Nat`. If the list contains fewer than `n` entries, then
the resulting list should be the input list. `#eval take 3 ["bolete", "oyster"]`
should yield `["bolete", "oyster"]`, and `#eval take 1 ["bolete", "oyster"]`
should yield `["bolete"]`.
-/

def take (list : List α) (n : Nat) : List α :=
  match list, n with
  | _, 0 => []
  | [], _ => []
  | head :: tail, n => head :: take tail (n - 1)

#eval take ["bolete", "oyster"] 3
#eval take ["bolete", "oyster"] 1

/-
Using the analogy between types and arithmetic, write a function that
distributes products over sums. In other words, it should have type
`α × (β ⊕ γ) → (α × β) ⊕ (α × γ)`.
-/

def f (x : α × (β ⊕ γ)) : (α × β) ⊕ (α × γ) :=
  match x with
  | (a, right) =>
    match right with
    | Sum.inl b => Sum.inl (a, b)
    | Sum.inr g => Sum.inr (a, g)

/-
Using the analogy between types and arithmetic, write a function that turns
multiplication by two into a sum. In other words, it should have type
`Bool × α → α ⊕ α`.
-/

def g (x : Bool × α) : α ⊕ α :=
  match x with
  | (Bool.true, x) => Sum.inl x
  | (Bool.false, x) => Sum.inr x
