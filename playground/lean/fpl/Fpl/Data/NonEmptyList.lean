structure NonEmptyList (α : Type) where
  head : α
  tail : List α
deriving Repr

instance : Coe (NonEmptyList α) (List α) where
  coe
    | nonEmptyList => nonEmptyList.head :: nonEmptyList.tail

#eval (List.length : List Nat → Nat) <| NonEmptyList.mk 1 [2, 3, 4]

instance : CoeDep (List α) (x :: xs) (NonEmptyList α) where
  coe := NonEmptyList.mk x xs

#eval (NonEmptyList.head : NonEmptyList Nat → Nat) [1, 2, 3, 4]

def NonEmptyList.append (a : NonEmptyList α) (b : NonEmptyList α)
: NonEmptyList α where
  head := a.head
  tail := a.tail ++ b.head :: b.tail

instance : Append (NonEmptyList α) where
  append := NonEmptyList.append

def nl1 : NonEmptyList Nat where
  head := 1
  tail := [2, 3, 4, 5]
def nl2 : NonEmptyList Nat where
  head := 6
  tail := [7, 8, 9, 10]
#eval nl1 ++ nl2
