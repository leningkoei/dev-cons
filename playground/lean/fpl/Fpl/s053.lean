namespace Exercise

/-!
Rewrite `evaluateM`, its helpers, and the different specific use cases using
`do`-notation instead of explicit calls to `>>=`.
-/

inductive Expr (op : Type) : Type
| const : Int → Expr op
| prim : op → Expr op → Expr op → Expr op

inductive Prim (special : Type) : Type
| plus : Prim special
| minus : Prim special
| times : Prim special
| other : special → Prim special

def applyPrim [Monad m] (applySpecial : special → Int → Int → m Int)
: Prim special → Int → Int → m Int
| Prim.plus, x, y => pure <| x + y
| Prim.minus, x, y => pure <| x - y
| Prim.times, x, y => pure <| x * y
| Prim.other op, x, y => applySpecial op x y

def evaluateM [Monad m] (applySpecial : special → Int → Int → m Int)
: Expr (Prim special) → m Int
| Expr.const i => pure i
| Expr.prim op e1 e2 => do
  let v1 ← evaluateM applySpecial e1
  let v2 ← evaluateM applySpecial e2
  applyPrim applySpecial op v1 v2

/-!
Rewrite `firstThirdFifthSeventh` using nested actions.
-/

def firstThirdFifthSeventh [Monad m] (lookup : List α → Nat → m α) (xs : List α)
: m (α × α × α × α):= do
  pure ((← lookup xs 0), (← lookup xs 2), (← lookup xs 4), (← lookup xs 6))

end Exercise
