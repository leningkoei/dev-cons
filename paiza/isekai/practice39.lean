def Pos : Type := {x : Nat // x > 0}

-- #print OfNat
instance : OfNat Pos (n + 1) where
  ofNat := ⟨n + 1, by simp_arith⟩

def Pos.toNat (n : Pos) : Nat := n.val
-- #print Add
instance : Add Pos where
  add x y := ⟨x.val + y.val, Nat.add_pos_left x.2 y.1⟩
instance : Sub Pos where
  sub x y := ⟨x.val - y.val, sorry⟩

inductive Item : Type where
| plus : Item
| minus: Item
| pos : Pos → Item

def Item.fromChar? (char : Char) : Option Item :=
  match char with
  | '+' => pure Item.plus
  | '-' => pure Item.minus
  | '1' => pure ∘ Item.pos <| 1
  | '2' => pure ∘ Item.pos <| 2
  | '3' => pure ∘ Item.pos <| 3
  | '4' => pure ∘ Item.pos <| 4
  | '5' => pure ∘ Item.pos <| 5
  | '6' => pure ∘ Item.pos <| 6
  | '7' => pure ∘ Item.pos <| 7
  | '8' => pure ∘ Item.pos <| 8
  | '9' => pure ∘ Item.pos <| 9
  | _ => Option.none

def read : IO (Option (List Item)) := do
  let stdin ← IO.getStdin
  let expr ← String.trim <$> stdin.getLine
  pure do
    let expr ←
      if expr.length < 1 then Option.none
      else if expr.length ≥ 10000 then Option.none
      else pure expr
    let expr ← expr.toList.mapM Item.fromChar?
    pure expr

def eval : List Item → Option Pos
| [Item.pos n] => pure n
| Item.pos n :: Item.plus :: restExpr => eval restExpr >>= pure ∘ (n + ·)
| Item.pos n :: Item.minus :: restExpr => eval restExpr >>= pure ∘ (n - ·)
| _ => Option.none

instance : ToString Pos where
  toString n := ToString.toString n.val
def print : Pos → IO Unit := IO.println

def main : IO Unit := do
  let readResult ← read
  let evalResult ← pure <| readResult >>= eval
  let stdout ← IO.getStdout
  match evalResult with
  | Option.none => stdout.putStrLn "Input does not satisfy condition."
  | Option.some n => print n
