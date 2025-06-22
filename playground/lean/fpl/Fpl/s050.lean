import Fpl.Control.Expect
import Fpl.Data.BinTree

namespace Note

def Option.andThen (opt : Option α) (next : α → Option β) : Option β :=
  match opt with
  | none => none
  | some x => next x

def Expect.andThen (attemp : Expect ε α) (next : α → Expect ε β) : Expect ε β :=
  match attemp with
  | Expect.error msg => Expect.error msg
  | Expect.ok x => next x

def isEven (x : Int) : Bool := x % 2 == 0

def sumAndFindEvens : List Int → List Int × Int
| [] => ([], 0)
| x :: xs =>
  let (moreEven, sum) := sumAndFindEvens xs
  let evenHere := if isEven x then [x] else []
  (evenHere ++ moreEven, x + sum)

def inorderSum : BinTree Int → List Int × Int
| BinTree.leaf => ([], 0)
| BinTree.branch l x r =>
  let (leftVisited, leftSum) := inorderSum l
  let (hereVisited, hereSum) := ([x], x)
  let (rightVisited, rightSum) := inorderSum r
  (leftVisited ++ hereVisited ++ rightVisited, leftSum + hereSum + rightSum)

structure WithLog (logged : Type) (α : Type) where
  log : List logged
  val : α

def WithLog.andThen (result : WithLog α β) (next : β → WithLog α γ)
: WithLog α γ :=
  let {log := thisOut, val := thisRes} := result
  let {log := nextOut, val := nextRes} := next thisRes
  {log := thisOut ++ nextOut, val := nextRes}

def ok (x : β) : WithLog α β := {log := [], val := x}
def save (data : α) : WithLog α Unit := {log := [data], val := ()}

def sumAndFindEvens' : List Int → WithLog Int Int
| [] => ok 0
| x :: xs =>
  WithLog.andThen (if isEven x then save x else ok ()) λ () =>
  WithLog.andThen (sumAndFindEvens' xs) λ sum =>
  ok (x + sum)

def inorderSum' : BinTree Int → WithLog Int Int
| BinTree.leaf => ok 0
| BinTree.branch l x r =>
  WithLog.andThen (inorderSum' l) λ leftSum =>
  WithLog.andThen (save x) λ () =>
  WithLog.andThen (inorderSum' r) λ rightSum =>
  ok (leftSum + x + rightSum)

def number (t : BinTree α) : BinTree (Nat × α) :=
  let rec helper (n : Nat) : BinTree α → (Nat × BinTree (Nat × α))
  | BinTree.leaf => (n, BinTree.leaf)
  | BinTree.branch l x r =>
    let (k, numberedLeft) := helper n l
    let (i, numberedRight) := helper (k + 1) r
    (i, BinTree.branch numberedLeft (k, x) numberedRight)
  (helper 0 t).snd

def State (σ : Type) (α : Type) : Type := σ → (σ × α)
def State.ok (x : α) : State σ α := λ s => (s, x)
def State.get : State σ σ := λ s => (s, s)
def State.set (s : σ) : State σ Unit := λ _ => (s, ())
def State.andThen (first : State σ α) (next : α → State σ β) : State σ β :=
  λ s =>
    let (s', x) := first s
    next x s'

def number' (t : BinTree α) : BinTree (Nat × α) :=
  let rec helper : BinTree α → State Nat (BinTree (Nat × α))
  | BinTree.leaf => State.ok BinTree.leaf
  | BinTree.branch l x r =>
    State.andThen (helper l) λ numberedLeft =>
    State.andThen State.get λ k =>
    State.andThen (State.set (k + 1)) λ () =>
    State.andThen (helper r) λ numberedRight =>
    State.ok (BinTree.branch numberedLeft (k, x) numberedRight)
  (helper t 0).snd

end Note
