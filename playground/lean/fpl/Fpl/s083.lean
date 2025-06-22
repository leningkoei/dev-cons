import Fpl.Data.Vect
import Fpl.Database.Row

namespace Notes

inductive DBType where
| int : DBType
| string : DBType
| bool : DBType

abbrev DBType.asType : DBType → Type
| DBType.int => Int
| DBType.string => String
| DBType.bool => Bool

instance {t : DBType} : BEq t.asType where -- compare a pair of value
  beq :=
    match t with
    | DBType.int
    | DBType.string
    | DBType.bool
    => BEq.beq
#eval (1 : DBType.int.asType) == (2 : DBType.int.asType)

instance : BEq DBType where -- compare the type of a pair of values
  beq
    | DBType.int, DBType.int => Bool.true
    | DBType.string, DBType.string => Bool.true
    | DBType.bool, DBType.bool => Bool.true
    | _, _ => Bool.false
#eval DBType.int == DBType.bool

-- instance (t : DBType) : Repr t.asType where
--   reprPrec :=
--     match t with
--     | DBType.int
--     | DBType.string
--     | DBType.bool
--     => Repr.reprPrec

structure Column : Type where
  name : String
  contains : DBType

abbrev Schema : Type := List Column

abbrev Row
: Schema → Type
| [] => Unit
| [col] => col.contains.asType
| col1 :: col2 :: cols => col1.contains.asType × Row (col2 :: cols)

abbrev Table
: Schema → Type
| s => List (Row s)

abbrev peak : Schema := -- create table
  [ ⟨"name", DBType.string⟩
  , ⟨"location", DBType.string⟩
  , ⟨"elevation", DBType.int⟩
  , ⟨"lastVisited", DBType.int⟩
  ]
def mountainDiary : Table peak := -- insert
  [ ("Mount Nebo",       "USA",     3637, 2013)
  , ("Moscow Mountain",  "USA",     1519, 2015)
  , ("Himmelbjerget",    "Denmark", 147,  2004)
  , ("Mount St. Helens", "USA",     2549, 2010)
  ]
#eval mountainDiary

abbrev waterfall : Schema :=
  [ ⟨"name", DBType.string⟩
  , ⟨"location", DBType.string⟩
  , ⟨"lastVisited", DBType.int⟩
  ]
def waterfallDiary : Table waterfall :=
  [ ("Multnomah Falls", "USA", 2018)
  , ("Shoshone Falls",  "USA", 2014)
  ]

def Row.beq
: Row s → Row s → Bool
| row1, row2 =>
  match s with
  | [] => Bool.true
  | [_] => row1 == row2
  | _::_::_ =>
    match row1, row2 with
    | (x, row1), (y, row2) => x == y && Row.beq row1 row2
instance : BEq (Row s) where
  beq := Row.beq

inductive HasCol : Schema → String → DBType → Type where
| here : HasCol (⟨name, t⟩ :: _) name t
| there : HasCol s name t → HasCol (_ :: s) name t
-- | here : HasCol s name t
-- | there : HasCol s name t → HasCol s name t
def hasColElevation : HasCol peak "elevation" DBType.int :=
  HasCol.there ∘ HasCol.there <| HasCol.here

/--
extract that column's value from a row
-/
def Row.get
: Row s → HasCol s n t → t.asType
| row, col =>
  match s, col, row with
  | [_], HasCol.here, (v) => v
  | _::_::_, HasCol.here, (v, _) => v
  | _::_::_, HasCol.there next, (_, r) => Row.get r next
#eval Row.get mountainDiary.head! hasColElevation
abbrev wtf : Schema := [ ⟨"id", DBType.int⟩ ]
def wtfs : Table wtf := [(1), (2), (3)]
#eval Row.get wtfs.tail!.head! HasCol.here

inductive Subschema : Schema → Schema → Type where
| nil : Subschema [] bigger
| cons
: HasCol bigger n t →
  Subschema smaller bigger →
  Subschema (⟨n, t⟩ :: smaller) bigger
def travelDiary : Schema :=
  [ ⟨"name", DBType.string⟩
  , ⟨"location", DBType.string⟩
  , ⟨"lastVisited", DBType.int⟩ ]
example : Subschema travelDiary peak :=
  Subschema.cons HasCol.here
    (Subschema.cons (HasCol.there <| HasCol.here)
      (Subschema.cons (HasCol.there ∘ HasCol.there ∘ HasCol.there <| HasCol.here)
        Subschema.nil))
example : Subschema travelDiary peak := by repeat constructor
example : Subschema [] peak := Subschema.nil
example : Subschema [] peak := by constructor
example : Subschema [⟨"location", DBType.string⟩] peak :=
  Subschema.cons (HasCol.there <| HasCol.here) Subschema.nil
example : Subschema [⟨"location", DBType.string⟩] peak := by
  constructor; constructor; constructor; constructor
example : Subschema [⟨"location", DBType.string⟩] peak := by repeat constructor

def Subschema.addColumn
: Subschema smaller bigger → Subschema smaller (column :: bigger)
| Subschema.nil => Subschema.nil
| Subschema.cons col sub =>
  Subschema.cons (HasCol.there col) sub.addColumn

def Subschema.reflexive
: (s : Schema) → Subschema s s
| [] => Subschema.nil
| _ :: cols =>
  Subschema.cons HasCol.here (Subschema.reflexive cols).addColumn

def Row.project
: Row s → (s' : Schema) → Subschema s' s → Row s'
| _row, [], Subschema.nil => ()
| row, [_], Subschema.cons col Subschema.nil => row.get col
| row, _a::b::c, Subschema.cons col cols =>
  (row.get col, row.project (b::c) cols)

def Table.project
: Table s → (s' : Schema) → Subschema s' s → Table s'
| table, s', prove => table.map (λ row ↦ row.project s' prove)
#eval mountainDiary.project travelDiary (by repeat constructor)

inductive DBExpr : (s : Schema) → DBType → Type where
| col : (n : String) → HasCol s n t → DBExpr s t
| eq : DBExpr s t → DBExpr s t → DBExpr s DBType.bool
| lt : DBExpr s DBType.int → DBExpr s DBType.int → DBExpr s DBType.bool
| and : DBExpr s DBType.bool → DBExpr s DBType.bool → DBExpr s DBType.bool
| const : t.asType → DBExpr s t

example : DBExpr peak DBType.bool :=
  DBExpr.and
    (DBExpr.lt (DBExpr.const 1000)
      (DBExpr.col "elevation" (HasCol.there ∘ HasCol.there <| HasCol.here)))
    (DBExpr.eq (DBExpr.const "Denmark")
      (DBExpr.col "location" (by repeat constructor)))
macro "c!" n:term : term => `(DBExpr.col $n (by repeat constructor))
def tallInDenmark : DBExpr peak DBType.bool :=
  DBExpr.and
    (DBExpr.lt (DBExpr.const 1000) (c! "elevation"))
    (DBExpr.eq (DBExpr.const "Denmark") (c! "location"))

def DBExpr.evaluate : Row s → DBExpr s t → t.asType
| row, DBExpr.col _ loc => row.get loc
| row, DBExpr.eq e1 e2 => e1.evaluate row == e2.evaluate row
| row, DBExpr.lt e1 e2 => e1.evaluate row < e2.evaluate row
| row, DBExpr.and e1 e2 => e1.evaluate row && e2.evaluate row
| _row, DBExpr.const v => v
#eval tallInDenmark.evaluate ("Valby Bakke", "Denmark", 31, 2023)
#eval tallInDenmark.evaluate ("Fictional mountain", "Denmark", 1031, 2023)
#eval tallInDenmark.evaluate ("Mount Borah", "USA", 3859, 1996)

def disjoint [BEq α]
: List α → List α → Bool
| xs, ys => not (xs.any ys.contains || ys.any xs.contains)
#eval disjoint [1,2,3,4] [5,6,7,8]

def Schema.renameColumn
: (s : Schema) → HasCol s n t → String → Schema
| c :: cs, HasCol.here, n' => {c with name := n'} :: cs
| c :: cs, HasCol.there next, n' => c :: Schema.renameColumn cs next n'

inductive Query : Schema → Type where
| table : Table s → Query s
| union : Query s → Query s → Query s
| diff : Query s → Query s → Query s
| select : Query s → DBExpr s DBType.bool → Query s
| project : Query s → (s' : Schema) → Subschema s' s → Query s'
| product
: Query s1 → Query s2 →
  disjoint (s1.map Column.name) (s2.map Column.name) = Bool.true →
  Query (s1 ++ s2)
| renameColumn
: Query s → (c : HasCol s n t) → (n' : String) →
  !((s.map Column.name).contains n') = Bool.true → Query (s.renameColumn c n')
| prefixWith
: (n : String) → Query s →
  Query (s.map λ c ↦ {c with name := n ++ "." ++ c.name})

/--
Add a single column to a row.
-/
def Row.addVal
: c.contains.asType → Row s → Row (c :: s)
| v, row =>
  match s, row with
  | [], () => v
  | _ :: _, v' => (v, v')
#eval ((1 : Row [⟨"name", DBType.int⟩]).addVal 1 : Row [⟨"fuck", DBType.int⟩, _])

def Row.append
: Row s1 → Row s2 → Row (s1 ++ s2)
| r1, r2 =>
  match s1, r1 with
  | [], () => r2
  | [_], v => r2.addVal v
  | _::_::_, (v, r') => (v, r'.append r2)

def Table.cartesianProduct
: Table s1 → Table s2 → Table (s1 ++ s2)
| t1, t2 => t1.flatMap λ r1 ↦ t2.map r1.append
def shit := mountainDiary.cartesianProduct mountainDiary
#eval mountainDiary.cartesianProduct mountainDiary

def List.without [BEq α]
: List α → List α → List α
| source, banned => source.filter λ a ↦ !(banned.contains a)
#eval List.without [1,2,3,4] [1,2,3]

def Row.rename
: (theCol : HasCol s n t) → Row s → Row (s.renameColumn theCol n')
| theCol, row =>
  match s, row, theCol with
  | [_], v, HasCol.here => v
  | _::_::_, (v, r), HasCol.here => (v, r)
  | _::_::_, (v, r), HasCol.there next => (r.rename next).addVal v
#eval (mountainDiary.head!.rename HasCol.here
  : Row
    [ ⟨"id", DBType.string⟩, ⟨"location", DBType.string⟩
    , ⟨"elevation", DBType.int⟩, ⟨"lastVisited", DBType.int⟩ ])
  -- : Row (peak.renameColumn HasCol.here "id"))
  -- : Row peak)
def Table.renameColumn
: (theCol : HasCol s n t) → Table s → Table (s.renameColumn theCol n')
| theCol, table => table.map (·.rename theCol)

def Row.prefix
: Row s → Row (s.map λ col ↦ {col with name := n ++ "." ++ col.name})
| row =>
  match s, row with
  | [], _ => ()
  | [_], v => v
  | _::_::_, (v, r) => addVal v r.prefix

def Query.exec
: Query s → Table s
| Query.table t => t
| Query.union q1 q2 => q1.exec ++ q2.exec
| Query.diff q1 q2 => List.without q1.exec q2.exec
| Query.select q e => q.exec.filter e.evaluate
| Query.project q s' subschema => q.exec.project s' subschema
| Query.product q1 q2 is_disjoint => Table.cartesianProduct q1.exec q2.exec
| Query.renameColumn q theCol n' s' => q.exec.renameColumn theCol
| Query.prefixWith prefix' q => q.exec.map (·.prefix)

/--
Finds the heights of all mountain peaks with an elevation greater than 500
meters.
-/
def example1 := project
where
  table := Query.table mountainDiary
  select := table.select
    (DBExpr.lt (DBExpr.const 500) (c! "elevation"))
  project := select.project
    [⟨"elevation", DBType.int⟩] (by repeat constructor)
#eval example1.exec

/--
Match all pairs mountains and waterfalls in the same location.
-/
def example2 := project where
  mountains := Query.table mountainDiary |>.prefixWith "mountainDiary"
  waterfalls := Query.table waterfallDiary |>.prefixWith "waterfallDiary"
  product := Query.product mountains waterfalls (by decide)
  select := product.select
    (DBExpr.eq (c! "mountainDiary.location") (c! "waterfallDiary.location"))
  project := select.project
    [ ⟨"mountainDiary.name", DBType.string⟩
    , ⟨"waterfallDiary.name", DBType.string⟩
    , ⟨"mountainDiary.location", DBType.string⟩
    ] (by repeat constructor)
#eval example2.exec

end Notes

namespace Exercises

/-! # Date
Define a structure to represent dates. Add it to the `DBType` universe and
update the rest of the code accordingly. Provide the extra `DBExpr` constructors
that seem to be necessary.
-/

-- Fpl.Database

/-! Nullable Types
Add support for nullable columns to the query language by representing database
types with the following structure:
```
structure NDBType where
  underlying : DBType
  nullable : Bool

abbrev NDBType.asType (t : NDBType) : Type :=
  if t.nullable
    then Option t.underlying.asType
    else t.underlying.asType
```
Use this type in place of DBType in Column and DBExpr, and lookup SQL's rules
for NULL and comparison operators to determine the types of DBExpr's
constructors.
-/

-- How can you define `instance {t : NDBType} : BEq t.asType`? answer from
-- -- https://github.com/leanprover/fp-lean/issues/154
-- How can you define `DBExpr.lt` for all `NDBType.nullable` which
-- -- `.DBType == int`?

/-! Experimenting with Tactics
What is the result of asking Lean to find values of the following types using
`by repeat constructor`? Explain why each gives the result that it does.
* `Nat`
* `List Nat`
* `Vect Nat 4`
* `Row []`
* `Row [⟨"price", .int⟩]`
* `Row peak`
* `HasCol [⟨"price", .int⟩, ⟨"price", .int⟩] "price" .int`
-/

def a : Nat := by repeat constructor
#eval a

def b : List Nat := by repeat constructor
#eval b

def c : Vect Nat 4 := by repeat constructor
#eval c

def d : Row [] := by repeat constructor
#eval d

def e : Row [⟨"price", ⟨.int, .false⟩⟩] := by repeat constructor
#eval e

def f : Row peak := by repeat constructor
#eval f

def g
: TheCol
  [⟨"price", ⟨.int, .false⟩⟩, ⟨"price", ⟨.int, .false⟩⟩]
  "price"
  ⟨.int, .false⟩
:= by repeat constructor
#eval g

end Exercises
