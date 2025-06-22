import Fpl.Data.BinTree

namespace Note

def State (σ : Type) (α : Type) : Type := σ → σ × α
def State.get : State σ σ := λ s => (s, s)
def State.set (s' : σ) : State σ Unit := λ _s => (s', ())

instance : Monad (State σ) where
  pure x := λ s => (s, x)
  bind first next := λ s =>
    let (s', x) := first s
    next x s'

def List.mapM [Monad m] (f : α → m β) : List α → m (List β)
| [] => pure []
| x :: xs => f x >>= λ x' => xs.mapM f >>= λ xs' => pure (x' :: xs')

def increment (howMuch : Int) : State Int Int :=
  State.get >>= λ i =>
  State.set (i + howMuch) >>= λ () =>
  pure i
#eval List.mapM increment [1, 2, 3, 4, 5] 0

structure WithLog (logged : Type) (α : Type) : Type where
  log : List logged
  val : α
def WithLog.save (data : logged) : WithLog logged Unit :=
  { log := [data], val := () }

instance : Monad (WithLog logged) where
  pure x := { log := [], val := x }
  bind result next :=
    let { log := thisOut, val := thisRes } := result
    let { log := nextOut, val := nextRes } := next thisRes
    { log := thisOut ++ nextOut, val := nextRes }

def saveIfEven (i : Int) : WithLog Int Int :=
  (if Int.isEven i then (WithLog.save i) else pure ())
  >>= λ () => pure i
  where
    Int.isEven (i : Int) := i % 2 == 0
#eval List.mapM saveIfEven [1, 2, 3, 4, 5]

end Note

namespace Exercise

/-- # Mapping on a Tree

Define a function `BinTree.mapM`. By analogy to `mapM` for lists, this function
should apply a monadic function to each data entry in a tree, as a preorder
traversal. The type signature should be:
```
def BinTree.mapM [Monad m] (f : α → m β) : BinTree α → m (BinTree β)
```
-/

def BinTree.mapM [Monad m] (f : α → m β) : BinTree α → m (BinTree β)
| BinTree.leaf => pure BinTree.leaf
| BinTree.branch l x r =>
  let mx' := f x
  let ml' := BinTree.mapM f l
  let mr' := BinTree.mapM f r
  mx' >>= λ x' => ml' >>= λ l' => mr' >>= λ r' =>
    pure <| BinTree.branch l' x' r'

def Note.WithLog.saveAll (i : α) : Note.WithLog α α :=
  Note.WithLog.save i >>= λ () => pure i
def binTreeA :=
  let node4 := BinTree.branch BinTree.leaf 4 BinTree.leaf
  let node5 := BinTree.branch BinTree.leaf 5 BinTree.leaf
  let node6 := BinTree.branch BinTree.leaf 6 BinTree.leaf
  let node7 := BinTree.branch BinTree.leaf 7 BinTree.leaf
  let node2 := BinTree.branch node4 2 node5
  let node3 := BinTree.branch node6 3 node7
  let node1 := BinTree.branch node2 1 node3
  node1
#eval binTreeA
#eval (BinTree.mapM Note.WithLog.saveAll binTreeA).log

/- # The Option Monad Contract

First, write a convincing argument that the `Monad` instance for `Option`
satisfies the monad contract. Then, consider the following instance:
```
instance : Monad Option where
  pure x := some x
  bind opt next := none
```
Both methods have the correct type. Why does this instance violate the monad
contract?

#### The Monad Contract:

`pure` should be a left identity of `bind`: `bind (pure v) f ≡ f v`

`pure` should be a right identity of `bind`: `bind v pure ≡ v`

`bind` should be associative: `bind (bind v f) g ≡ bind v (λ x => bind (f x) g)`
-/

inductive Option (α : Type) : Type
| none : Option α
| some : α → Option α

instance : Monad Option where
  pure x := Option.some x
  bind _opt _next := Option.none
#eval bind (m := Option) (pure 1) (λ x => pure x)
#eval (λ x => (pure : Nat → Option Nat) x) 1
#eval bind (m := Option) (pure 1) pure
#eval (pure : Nat → Option Nat) 1

instance : Monad Option where
  pure := Option.some
  bind
  | Option.none, _ => Option.none
  | Option.some x, f => f x
#eval bind (m := Option) (pure 1) (λ x => pure x)
#eval (λ x => (pure : Nat → Option Nat) x) 1
#eval bind (m := Option) (pure 1) pure
#eval (pure : Nat → Option Nat) 1

end Exercise
