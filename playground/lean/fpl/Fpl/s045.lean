#check 3 < 4
#eval if 3 < 5 then "True" else "False"

namespace Note

inductive BinTree (α : Type) where
| leaf : BinTree α
| branch : BinTree α → α → BinTree α → BinTree α

def BinTree.eq [BEq α] : BinTree α → BinTree α → Bool
| BinTree.leaf, BinTree.leaf => Bool.true
| BinTree.branch l x r, BinTree.branch l' x' r' =>
  x == x' && l.eq l' && r.eq r'
| _, _ => Bool.false
instance [BEq α] : BEq (BinTree α) where
  beq := BinTree.eq

def BinTree.hash [Hashable α] : BinTree α → UInt64
| BinTree.leaf => 0
| BinTree.branch l x r =>
  mixHash 1 ∘ mixHash l.hash ∘ mixHash (Hashable.hash x) <| r.hash
instance [Hashable α] : Hashable (BinTree α) where
  hash := BinTree.hash
-- instance : [Hashable α] → [Hashable (BinTree α)] → Hashable (BinTree α) where
--   hash
--   | BinTree.leaf => 0
--   | BinTree.branch l x r =>
--     List.foldr (mixHash . .) (hash r) [1, hash l, hash x]

end Note

namespace Exercise

/-
Write an instance of `HAppend (List α) (NonEmptyList α) (NonEmptyList α)` and
test it.
-/

structure NonEmptyList (α : Type) where
  head : α
  tail : List α

instance : HAppend (List α) (NonEmptyList α) (NonEmptyList α) where
  hAppend
  | [], neList => neList
  | head :: tail, neList => {
      head := head
      tail := tail ++ neList.head :: neList.tail
  }

#eval [1, 2, 3, 4] ++ NonEmptyList.mk 1 [2, 3, 4]

/-
Implement a `Functor` instance for the binary tree datatype.
-/

inductive BinTree (α : Type) where
| leaf : BinTree α
| branch : BinTree α → α → BinTree α → BinTree α

def BinTree.map : BinTree α → (α → β) → BinTree β
| BinTree.leaf, _ => BinTree.leaf
| BinTree.branch l x r, f => BinTree.branch (l.map f) (f x) (r.map f)
instance : Functor BinTree where
  map := flip BinTree.map
-- instance : [Functor BinTree] → Functor BinTree where
--   map
--   | _, BinTree.leaf => BinTree.leaf
--   | f, BinTree.branch l x r =>
--     BinTree.branch (f <$> l) (f x) (f <$> r)

def BinTree.obj1 := BinTree.branch BinTree.leaf 1 BinTree.leaf
def BinTree.obj2 := BinTree.branch BinTree.leaf 2 BinTree.leaf
def BinTree.obj3 := BinTree.branch BinTree.obj1 3 BinTree.obj2

#eval (. + 1) <$> BinTree.obj3

end Exercise
