import Fpl.Control.Expect
import Fpl.Control.WithLog

namespace Note

inductive Expr (op : Type) : Type where
| const : Int → Expr op
| prim : op → Expr op → Expr op → Expr op

inductive Arith : Type where
| plus : Arith
| minus : Arith
| times : Arith
| div : Arith

open Expr in
open Arith in
def twoPlusThree : Expr Arith :=
  prim plus (const 2) (const 3)

open Expr in
open Arith in
def divZero : Expr Arith :=
  prim div (const 7) (const 0)

-- def evaluateOption : Expr Arith → Option Int
-- | Expr.const i => pure i
-- | Expr.prim p e1 e2 =>
--   evaluateOption e1 >>= λ v1 =>
--   evaluateOption e2 >>= λ v2 =>
--   match p with
--   | Arith.plus => pure <| v1 + v2
--   | Arith.minus => pure <| v1 - v2
--   | Arith.times => pure <| v1 * v2
--   | Arith.div => if v2 == 0 then Option.none else pure <| v1 / v2

def applyDivExpect (x : Int) : Int → Expect String Int
| 0 => Expect.error s!"Tried to divide {x} by zero"
| y => pure <| x / y

def applyDivOption (x : Int) : Int → Option Int
| 0 => Option.none
| y => pure <| x / y

-- def applyPrim [Monad m] (applyDiv : Int → Int → m Int)
-- : Arith → Int → Int → m Int
-- | Arith.plus, x, y => pure (x + y)
-- | Arith.minus, x, y => pure (x - y)
-- | Arith.times, x, y => pure (x * y)
-- | Arith.div, x, y => applyDiv x y
--
-- def Expr.evaluate [Monad m] (applyPrim : Arith → Int → Int → m Int)
-- : Expr Arith → m Int
-- | Expr.const i => pure i
-- | Expr.prim p e1 e2 =>
--   e1.evaluate applyPrim >>= λ v1 =>
--   e2.evaluate applyPrim >>= λ v2 =>
--   applyPrim p v1 v2
--
-- #eval divZero.evaluate (applyPrim applyDivOption)
-- #eval divZero.evaluate (applyPrim applyDivExpect)

inductive Prim (special : Type) : Type where
| plus : Prim special
| minus : Prim special
| times : Prim special
| other : special → Prim special

inductive CanFail : Type where
| div : CanFail

def divOption : CanFail → Int → Int → Option Int
| CanFail.div, x, y => if y == 0 then none else pure (x / y)

def divExpect : CanFail → Int → Int → Expect String Int
| CanFail.div, x, 0 => Expect.error s!"Tried to divide {x} by zero"
| CanFail.div, x, y => pure <| x / y

def applyPrim [Monad m] (applySpecial : special → Int → Int → m Int)
: Prim special → Int → Int → m Int
| Prim.plus, x, y => pure <| x + y
| Prim.minus, x, y => pure <| x - y
| Prim.times, x, y => pure <| x * y
| Prim.other special, x, y => applySpecial special x y

def Expr.evaluate [Monad m] (applySpecial : special → Int → Int → m Int)
: Expr (Prim special) → m Int
| Expr.const i => pure i
| Expr.prim p e1 e2 =>
  e1.evaluate applySpecial >>= λ v1 =>
  e2.evaluate applySpecial >>= λ v2 =>
  applyPrim applySpecial p v1 v2

def divZero' : Expr (Prim CanFail) :=
  Expr.prim (Prim.other CanFail.div) (Expr.const 7) (Expr.const 0)
#eval divZero'.evaluate divOption
#eval divZero'.evaluate divExpect

def noSpecial [Monad m] (op : Empty) : Int → Int → m Int
| _, _ => nomatch op

def noSpecialPrim : Expr (Prim special) :=
  Expr.prim Prim.plus (Expr.const 5) (Expr.const (-14))
#eval noSpecialPrim.evaluate (m := Id) noSpecial

inductive Many (α : Type) : Type where
| none : Many α
| more : α → (Unit → Many α) → Many α

def Many.one (x : α) : Many α := Many.more x (λ () => Many.none)

def Many.union : Many α → Many α → Many α
| Many.none, ys => ys
| Many.more x xs, ys => Many.more x (λ () => Many.union (xs ()) ys)

def Many.fromList : List α → Many α
| [] => Many.none
| x :: xs => Many.more x (λ () => Many.fromList xs)

def Many.take : Nat → Many α → List α
| 0, _ => []
| _, Many.none => []
| n + 1, Many.more x xs => x :: (xs ()).take n

def Many.takeAll : Many α → List α
| Many.none => []
| Many.more x xs => x :: (xs ()).takeAll

def Many.bind : Many α → (α → Many β) → Many β
| Many.none, _ => Many.none
| Many.more x xs, f =>
  let xs := xs ()
  (f x).union (xs.bind f)

instance : Monad Many where
  pure := Many.one
  bind := Many.bind

def addsTo (goal : Nat) : List Nat → Many (List Nat)
| [] => if goal == 0 then pure [] else Many.none
| x :: xs =>
  if x > goal
  then addsTo goal xs
  else
    (addsTo goal xs).union
      (addsTo (goal - x) xs >>= λ answer =>
        pure (x :: answer))

inductive NeedsSearch : Type where
| div : NeedsSearch
| choose : NeedsSearch

def applySearch : NeedsSearch → Int → Int → Many Int
| NeedsSearch.choose, x, y => Many.fromList [x, y]
| NeedsSearch.div, x, y =>
  if y == 0
  then Many.none
  else Many.one <| x / y

#eval (Expr.evaluate
        applySearch
        (Expr.prim
          Prim.plus
          (Expr.const 1)
          (Expr.prim
            (Prim.other NeedsSearch.choose) (Expr.const 2) (Expr.const 5)
          ))).takeAll
#eval (Expr.evaluate
        applySearch
        (Expr.prim
          Prim.plus
          (Expr.const 1)
          (Expr.prim
            (Prim.other NeedsSearch.div)
            (Expr.const 2)
            (Expr.const 0)))).takeAll


def Reader (ρ : Type) (α : Type) : Type := ρ → α
def Reader.read : Reader ρ ρ := λ env => env
def Reader.pure (x : α) : Reader ρ α := λ _ => x
def Reader.bind
-- {ρ : Type} {α : Type} {β : Type}
(result : Reader ρ α) (next : α → Reader ρ β) : Reader ρ β :=
  λ env => next (result env) env
  -- λ rho =>
  --   let alpha := result rho
  --   let beta := next alpha rho
  --   beta

/--
### `Reader.bind (Reader.pure v) f ≡ f v`
```
bind (pure v) f ===>
bind (λ _ => v) f ==>
λ env => f ((λ _ => v) env) env ==>
λ env => f v env ==>
f v
```
### `Reader.bind r Reader.pure ≡ r`
```
bind r pure ==>
λ env => pure (r env) env ==>
λ env => (λ _ => r env) env ==>
λ env => r env ==>
r
```
### `Reader.bind (Reader.bind r f) g ≡ Reader.bind r (λ x => Reader.bind (f x) g)`
```
r >>= f >>= g ==>
λ env => g ((r >>= f) env) env ==>
λ env => g ((λ env' => f (r env') env') env) env ==>
λ env => g (f (r env) env) env
```
```
r >>= (λ x => f x >>= g) ==>
λ env => (λ x => f x >>= g) (r env) env ==>
λ env => (f (r env) >>= g) env ==>
λ env => (λ env' => g (f (r env) env') env') env ==>
λ env => g (f (r env) env) env
```
-/
instance : Monad (Reader ρ) where
  pure := Reader.pure
  bind := Reader.bind

abbrev Env : Type := List (String × (Int → Int → Int))

def exampleEnv : Env := [("max", max), ("mod", (· % ·))]

def applyPrimReader (op : String) (x : Int) (y : Int) : Reader Env Int :=
  Reader.read >>= λ env =>
  match env.lookup op with
  | Option.none => pure 0
  | Option.some f => pure (f x y)

#check Expr.evaluate
#eval
  (Expr.evaluate
    applyPrimReader
    (Expr.prim
      (Prim.other "max")
      (Expr.prim Prim.plus (Expr.const 5) (Expr.const 4))
      (Expr.prim Prim.times (Expr.const 3) (Expr.const 2))))
  exampleEnv

end Note

namespace Exercise

/-! Checking Contracts
Check the monad contract for `State σ` and `Expect ε`.
-/

def State (σ : Type) (α : Type) : Type := σ → σ × α
def State.pure (a : α) : State σ α := λ s => (s, a)
def State.bind (result : State σ α) (next : α → State σ β) : State σ β := λ s =>
  let (s', a) := result s
  next a s'

/--
### `pure v >>= f ≡ f v`
```
λ s => let (s', a) := pure v s in (f a) s' ==>
λ s => let (s', a) := (λ s'' => (s'', v) s) in (f a) s' ==>
λ s => let (s', a) := (s, v) in (f a) s' ==>
λ s => (f v) s ==>
f v
```
### `mv >>= pure ≡ mv`
```
λ s => let (s', a) := mv s in (pure a) s' ==>
λ s => let (s', a) := mv s in (λ s'' => (s'', a)) s' ==>
λ s => let (s', a) := mv s in (s', a) ==>
λ s => mv s ==>
mv
```
### `mv >>= f >>= g ≡ mv >>= (λ v => f v >>= g)`
#### `mv >>= f >>= g`
```
λ s2 => let (s2', a2) := (mv >>= f) s2 in g a2 s2' ==>
λ s2 => let (s2', a2) := (λ s1 => let (s1', a1) := mv s1 in f a1 s1') s2 in g a2 s2' ==>
λ s2 => let (s2', a2) := (let (s1', a1) := mv s2 in f a1 s1') in g a2 s2' ==>
λ s => let (s2', a2) := (let (s1', a1) := mv s in f a1 s1') in g a2 s2' ==>
λ s => let (s2', a2) := f (snd (mv s)) (fst (mv s)) in g a2 s2'
```
#### `mv >>= (λ v => f v >>= g)`
```
λ s => let (s1', a1) := (mv s) in (λ v => f v >>= g) a1 s1' ==>
λ s => let (s1', a1) := (mv s) in (f a1 >>= g) s1' ==>
λ s => let (s1', a1) := (mv s) in (λ s2 => let (s2', a2) := (f a1) s2 in g a2 s2') s1' ==>
λ s => let (s1', a1) := (mv s) in (let (s2', a2) := f a1 s1' in g a2 s2') ==>
λ s => let (s2', a2) := f (snd (mv s)) (fst (mv s)) in g a2 s2'
```
-/
instance : Monad (State σ) where
  pure := State.pure
  bind := State.bind

inductive Expect (ε : Type) (α : Type) : Type
| error : ε → Expect ε α
| ok : α → Expect ε α
def Expect.pure : α → Expect ε α := Expect.ok
def Expect.bind (result : Expect ε α) (next : α → Expect ε β) : Expect ε β :=
  match result with
  | Expect.error msg => Expect.error msg
  | Expect.ok v => next v

/--
### `pure v >>= f ≡ f v`
```
Expect.ok v >>= f ==>
f v
```
### `mv >>= pure ≡ mv`
#### `mv := Expect.ok v`
```
Expect.ok v >>= pure ==>
pure v ==>
Expect.ok v ==>
mv
```
#### `mv := Expect.error msg`
```
Expect.error msg >>= pure ==>
Expect.error msg ==>
mv
```
### `mv >>= f >>= g ≡ mv >>= (λ v => f v >>= g)`
#### `mv >>= f >>= g`
```
Expect.ok v >>= f >>= g ==>
f v >>= g
```
#### `mv >>= (λ v => f v >>= g)`
```
Expect.ok v >>= (λ v => f v >>= g) ==>
(λ v => f v >>= g) v ==>
f v >>= g
```
-/
instance : Monad (Expect ε) where
  pure := Expect.pure
  bind := Expect.bind

/-! Readers with Failure
Adapt the reader moand example so that it can also indicate failure when the
custom operator is not definded, rather than just returing zero. In other words,
given these definitions:
```
def ReaderOption (ρ : Type) (α : Type) : Type := ρ → Option α
def ReaderExpect (ε : Type) (ρ : Type) (α : Type) : Type := ρ → Expect ε α
```
do the following:
1. Write suitable `pure` and `bind` functions
2. Check that these functions satisfy the `Monad` contract
3. Write `Monad` instances for `ReaderOption` and `ReaderExpect`
4. Define suitable `applyPrim` operators and test then with `evaluateM` on some
expressions
-/

def ReaderOption (ρ : Type) (α : Type) : Type := ρ → Option α
def ReaderOption.pure (x : α) : ReaderOption ρ α := λ _ => Option.some x
def ReaderOption.bind
  (result : ReaderOption ρ α) (next : α → ReaderOption ρ β)
: ReaderOption ρ β := λ env =>
  match result env with
  | Option.none => Option.none
  | Option.some x => next x env
def ReaderOption.read : ReaderOption ρ ρ := λ env => Option.some env

def ReaderExpect (ε : Type) (ρ : Type) (α : Type) : Type := ρ → Expect ε α
def ReaderExpect.pure (x : α) : ReaderExpect ε ρ α := λ _ => Expect.ok x
def ReaderExpect.bind
  (result : ReaderExpect ε ρ α) (next : α → ReaderExpect ε ρ β)
: ReaderExpect ε ρ β := λ env =>
  match result env with
  | Expect.error msg => Expect.error msg
  | Expect.ok x => next x env
def ReaderExpect.read : ReaderExpect ε ρ ρ := λ env => Expect.ok env

instance : Monad (ReaderOption ρ) where
  pure := ReaderOption.pure
  bind := ReaderOption.bind

instance : Monad (ReaderExpect ε ρ) where
  pure := ReaderExpect.pure
  bind := ReaderExpect.bind

inductive Expr (op : Type) : Type where
| const : Int → Expr op
| prim : op → Expr op → Expr op → Expr op

inductive Arith : Type where
| plus : Arith
| minus : Arith
| times : Arith
| div : Arith
deriving BEq, Repr

instance : ToString Arith where
  toString
  | Arith.plus => "plus"
  | Arith.minus => "minus"
  | Arith.times => "times"
  | Arith.div => "div"

def Env : Type := List (Arith × (Int → Int → Int))
def env : Env := [
  (Arith.plus, (· + ·)),
  (Arith.minus, (· - ·)),
  (Arith.times, (· * ·)),
  -- (Arith.div, (· / ·)),
]

def applyPrimReaderOption (op : Arith) (v1 : Int) (v2 : Int)
: ReaderOption Env Int :=
  ReaderOption.read >>= λ env =>
  match env.lookup op with
  | Option.none => λ _ => Option.none
  | Option.some f => pure <| f v1 v2

def applyPrimReaderExpect (op : Arith) (v1 : Int) (v2 : Int)
: ReaderExpect String Env Int :=
  ReaderExpect.read >>= λ env =>
  match env.lookup op with
  | Option.none => λ _ =>
    Expect.error s!"Your operator `{op}` is not included in `env`"
  | Option.some f => pure <| f v1 v2

def evaluateM [Monad m] (applyPrim : Arith → Int → Int → m Int)
: Expr Arith → m Int
| Expr.const x => pure x
| Expr.prim p e1 e2 =>
  evaluateM applyPrim e1 >>= λ v1 =>
  evaluateM applyPrim e2 >>= λ v2 =>
  applyPrim p v1 v2

def timesZero := Expr.prim Arith.times (Expr.const 1) (Expr.const 0)
def divZero := Expr.prim Arith.div (Expr.const 1) (Expr.const 0)
def timesZeroAfterDivZero := Expr.prim Arith.times (Expr.const 0) divZero

#eval evaluateM applyPrimReaderOption timesZero env
#eval evaluateM applyPrimReaderOption divZero env
#eval evaluateM applyPrimReaderOption timesZeroAfterDivZero env
#eval evaluateM applyPrimReaderExpect timesZero env
#eval evaluateM applyPrimReaderExpect divZero env
#eval evaluateM applyPrimReaderExpect timesZeroAfterDivZero env


/-! # A Tracing Evaluator
The `WithLog` type can be used with the evaluator to add optional tracing of
some operators. In particular, the type `ToTrace` can serve as a signal to trace
a given operator:
```
inductive ToTrace (α : Type) : Type where
| trace : α → ToTrace α
```
For the tracing evaluator, expressions should have type
`Expr (Prim (ToTrace (Prim Empty)))`. This says that the operators in the
expression consist of addition, subtraction, and multiplication, augmented with
traced versions of each. The innermost argument is `Empty` to signal that there
are no further special operators inside of `trace`, only the three basic ones.

Do the following:
1. Implement a `Monad (WithLog logged)` instance
2. Write an `applyTraced` function to apply traced operators to their arguments,
logging both the operator and the arguments, with type
`ToTrace (Prim Empty) → Int → Int → WithLog (Prim Empty × Int × Int)`

If the exercise has been completed correctly, then
```
open Expr Prim ToTrace in
#eval evaluateM applyTraced (prim (other (trace times)) (prim (other (trace plus)) (const 1) (const 2)) (prim (other (trace minus)) (const 3) (const 4)))
```
should result in
```
{ log := [(Prim.plus, 1, 2), (Prim.minus, 3, 4), (Prim.times, 3, -1)], val := -3 }
```
Hint: values of type `Prim Empty` will appear in the resulting log. In order to
display them as a result of `#eval`, the following instances are required:
```
deriving instance Repr for WithLog
deriving instance Repr for Empty
deriving instance Repr for Prim
```
-/

inductive ToTrace (α : Type) : Type where
| trace : α → ToTrace α

inductive Prim (special : Type) : Type
| plus : Prim special
| minus : Prim special
| times : Prim special
| other : special → Prim special
deriving Repr

def applyTraced (op : Arith) (v1 : Int) (v2 : Int)
: WithLog (Arith × Int × Int) Int :=
  let val :=
    match op with
    | Arith.plus => (v1 + v2)
    | Arith.minus => (v1 - v2)
    | Arith.times => (v1 * v2)
    | Arith.div => (v1 / v2)
  WithLog.mk [(op, v1, v2)] val

#eval evaluateM applyTraced
  (Expr.prim Arith.times
    (Expr.prim Arith.plus (Expr.const 1) (Expr.const 2))
    (Expr.prim Arith.minus (Expr.const 3) (Expr.const 4)))

def applyTraced' (op : ToTrace (Prim Empty)) (x : Int) (y : Int)
: WithLog (Prim Empty × Int × Int) Int :=
  let op := match op with
  | ToTrace.trace op => op
  let val := match op with
  | Prim.plus => x + y
  | Prim.minus => x - y
  | Prim.times => x * y
  -- no special will be called!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
  WithLog.mk [(op, x, y)] val

def applyPrim [Monad m] (applySpecial : special → Int → Int → m Int)
: Prim special → Int → Int → m Int
| Prim.plus, x, y => pure <| x + y
| Prim.minus, x, y => pure <| x - y
| Prim.times, x, y => pure <| x * y
| Prim.other op, x, y => applySpecial op x y

def evaluateM' [Monad m] (applySpecial : special → Int → Int → m Int)
: Expr (Prim special) → m Int
| Expr.const x => pure x
| Expr.prim op e1 e2 =>
  evaluateM' applySpecial e1 >>= λ v1 =>
  evaluateM' applySpecial e2 >>= λ v2 =>
  applyPrim applySpecial op v1 v2

#eval evaluateM' applyTraced'
  (Expr.prim (Prim.other (ToTrace.trace Prim.times))
    (Expr.prim (Prim.other (ToTrace.trace Prim.plus))
      (Expr.const 1) (Expr.const 2))
    (Expr.prim (Prim.other (ToTrace.trace Prim.minus))
      (Expr.const 3) (Expr.const 4)))

end Exercise
