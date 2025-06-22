import Fpl.Database.Row
import Fpl.Database.Schema

-- inductive DBExpr : (s : Schema) → DBType → Type where
-- | col : (n : String) →  TheCol s n t → DBExpr s t
-- | eq : DBExpr s t → DBExpr s t → DBExpr s .bool
-- | lt : DBExpr s .int → DBExpr s .int → DBExpr s .bool
-- | and : DBExpr s .bool → DBExpr s .bool → DBExpr s .bool
-- | const : t.asType → DBExpr s t
inductive DBExpr : (s : Schema) → NDBType → Type where
| col : (n : String) →  TheCol s n t → DBExpr s t
| eq : DBExpr s t → DBExpr s t → DBExpr s ⟨.bool, .false⟩
| lt_nullable : DBExpr s ⟨.int, .true⟩ → DBExpr s ⟨.int, .true⟩ → DBExpr s ⟨.bool, .false⟩
| and : DBExpr s ⟨.bool, .false⟩ → DBExpr s ⟨.bool, .false⟩ → DBExpr s ⟨.bool, .false⟩
| const : t.asType → DBExpr s t

-- method

def DBExpr.evaluate
: DBExpr s t → Row s → t.asType
| col _n theCol, row => row.get theCol
| eq e1 e2, row => e1.evaluate row == e2.evaluate row
-- | lt e1 e2, row => e1.evaluate row < e2.evaluate row
| lt_nullable e1 e2, row =>
  match e1.evaluate row, e2.evaluate row with
  | .none, .none => .false
  | .none, _ => .true
  | _, .none => .false
  | .some x', .some y' => if x' < y' then .true else .false
-- | and e1 e2, row => e1.evaluate row ∧ e2.evaluate row
| and e1 e2, row =>
  let x : Bool := e1.evaluate row
  let y : Bool := e2.evaluate row
  let result : Bool := x ∧ y
  result
| const v, _ => v

-- other

macro "c!" n:term : term => `(DBExpr.col $n (by repeat constructor))

-- example

-- def tallInDenmark : DBExpr peak .bool :=
--   .and
--     (.lt (.const 1000) (c! "elevation")) -- elevation > 1000
--     (.eq (.const "Denmark") (c! "location")) -- location = Denmark
-- def tallInUSA : DBExpr peak .bool :=
--   .and
--     (.lt (.const 1000) (c! "elevation")) -- elevation > 1000
--     (.eq (.const "USA") (c! "location")) -- location = USA
--
-- #eval tallInDenmark.evaluate himmelbjergetDiary -- elevation ≯ 1000
-- #eval tallInDenmark.evaluate neboDiary -- location ≠ Denmark
-- #eval tallInDenmark.evaluate
--   ("Fictional mountain", "Denmark", 1230, date!(2023, 02, 28))
def tallInDenmark : DBExpr peak ⟨.bool, .false⟩ :=
  .and
    -- (.lt_nullable (.const (.some 1000)) (.col "elevation" elevation)) -- elevation > 1000
    (.lt_nullable (.const (.some 1000)) (c! "elevation")) -- elevation > 1000
    (.eq (@DBExpr.const peak ⟨.string, .false⟩ "Denmark") (c! "location")) -- location = Denmark
def tallInUSA : DBExpr peak ⟨.bool, .false⟩ :=
  .and
    (.lt_nullable (.const (.some 1000)) (c! "elevation")) -- elevation > 1000
    (.eq (@DBExpr.const peak ⟨.string, .false⟩ "USA") (c! "location")) -- location = USA

#eval tallInDenmark.evaluate himmelbjergetDiary -- elevation ≯ 1000
#eval tallInDenmark.evaluate neboDiary -- location ≠ Denmark
#eval tallInDenmark.evaluate
  ("Fictional mountain", "Denmark", (.some 1230), date!(2023, 02, 28))
