import Fpl.Database.Schema

abbrev Row : Schema → Type
| [] => Unit
| [col] => col.dbtype.asType
| col1 :: col2 :: cols => col1.dbtype.asType × Row (col2 :: cols)

-- instance

def Row.beq
: Row s → Row s → Bool
| r1, r2 =>
  match s with
  | [] => .true
  | [_] => r1 == r2
  | _::_::_ =>
    match r1, r2 with
    | (c1, r1'), (c2, r2') =>
      c1 == c2 && Row.beq r1' r2'
instance : BEq (Row s) where
  beq := Row.beq

-- util

-- def disjoint [BEq α]
-- : List α → List α → Bool
-- | xs, ys =>
--   let anyXsInYs := xs.any ys.contains
--   let anyYsInXs := ys.any xs.contains
--   not anyXsInYs ∧ not anyYsInXs

-- method

def Row.get
: Row schema → TheCol schema name dbtype → dbtype.asType
| row, theCol =>
  match schema, theCol, row with -- schema must be the first
  | [_], .here, (value) => value
  | _::_::_, .here, (value, _row) => value
  | _::_::_, .there next, (_value, row) => row.get next

def Row.getWithName
: Row s → (n : String) → TheCol s n t → t.asType
| row, _n, theCol => row.get theCol

def Row.project
: Row schema → (targetSchema : Schema) → Subschema targetSchema schema
→ Row targetSchema
| row, targetSchema, subschema =>
  match targetSchema, subschema with
  | [], .nil => ()
  | [_], .cons theCol .nil => row.get theCol
  | _::b::c, .cons theCol restRow =>
    (row.get theCol, row.project (b::c) restRow)

def Row.addVal
: Row s → c.dbtype.asType → Row (c :: s)
| row, v =>
  match s with
  | [] => v
  | _::_ => (v, row)

def Row.append
: Row s1 → Row s2
-- → disjoint (s1.map Column.name) (s2.map Column.name)
→ Row (s1 ++ s2)
| r1, r2 =>
  match s1, r1 with
  | [], () => r2
  | [_], (c1) => r2.addVal c1
  | _a::_b::_c, (c1, r1) => (c1, r1.append r2,)

def Row.rename
: Row s → (c : TheCol s n t) → Row (s.renameColumn c n')
| row, c =>
  match s, c with
  | [_], .here => row
  | _x1::x2::xs, .here => row
  | _x1::_x2::xs, .there next => row.snd.rename next |>.addVal row.fst

def Row.prefixWith
: Row s → (n : String) → Row (s.map λ c => {c with name := s!"{n}.{c.name}"})
| row, n =>
  match s with
  | [] => row
  | [_] => row
  | _::_::_ => row.snd.prefixWith n |>.addVal row.fst

-- example

-- abbrev neboDiary : Row peak := ("Mount Nebo", "USA", 3637, date!(2013, 02, 28))
-- abbrev moscowDiary : Row peak := ("Moscow Mountain", "USA", 1519, date!(2015, 02, 28))
-- abbrev himmelbjergetDiary : Row peak := ("Himmelbjerget", "Denmark", 147, date!(2004, 02, 29))
-- abbrev helensDiary : Row peak := ("Mount St. Helens", "USA", 2549, date!(2010, 02, 28))
-- #eval neboDiary
abbrev neboDiary : Row peak := ("Mount Nebo", "USA", (.some 3637), date!(2013, 02, 28))
abbrev moscowDiary : Row peak := ("Moscow Mountain", "USA", (.some 1519), date!(2015, 02, 28))
abbrev himmelbjergetDiary : Row peak := ("Himmelbjerget", "Denmark", (.some 147), date!(2004, 02, 29))
abbrev helensDiary : Row peak := ("Mount St. Helens", "USA", (.some 2549), date!(2010, 02, 28))
#eval neboDiary

abbrev multnomahDiary : Row waterfall := ("Multnomah Falls", "USA", date!(2018, 02, 28))
abbrev shoshoneDiary : Row waterfall := ("Shoshone Falls", "USA", date!(2014, 02, 28))

#eval neboDiary.get .here
#eval neboDiary.get (.there (.there .here))
#eval neboDiary.get (.there ∘ .there <| .here)
#eval neboDiary.getWithName "location" (by repeat constructor)
