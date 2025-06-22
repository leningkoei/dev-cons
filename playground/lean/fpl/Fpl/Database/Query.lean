import Fpl.Database.DBExpr
import Fpl.Database.Table

def disjoint [BEq α]
: List α → List α → Bool
| xs, ys =>
  let anyXsInYs := xs.any ys.contains
  let anyYsInXs := ys.any xs.contains
  not anyXsInYs ∧ not anyYsInXs

inductive Query : Schema → Type where
| table : Table s → Query s
/--
The union of two expressions that have the same schema combines the rows that
result from two queries.
-/
| union : Query s → Query s → Query s
/--
The difference of two expressions that have the same schema removes rows found
in the second result from the rows in the first result.
-/
| diff : Query s → Query s → Query s
/--
Selection by some criterion filters the result of a query according to an
expression.
-/
-- | select : Query s → DBExpr s .bool → Query s
| select : Query s → DBExpr s ⟨.bool, .false⟩ → Query s
/--
Projection into a subschema, removing columns from the result of a query.
-/
| project : Query s → (s' : Schema) → Subschema s' s → Query s'
/--
Cartesian product, combining every row from one query with every row from
another.
-/
| product
: Query s1 → Query s2
→ disjoint (s1.map Column.name) (s2.map Column.name)
→ Query (s1 ++ s2)
/--
Renaming a column in the result of a query, which modifies its schema
-/
| renameColumn
: Query s → (c : TheCol s n t) → (n' : String)
→ !((s.map Column.name).contains n') → Query (s.renameColumn c n')
/--
Prefixing all columns in a query with a name.
-/
| prefixWith
: Query s → (n : String)
→ Query (s.map λ c => {c with name := s!"{n}.{c.name}"})

-- method

def Query.exec
: Query s → Table s
| .table t => t
| .union q1 q2 => q1.exec ++ q2.exec
| .diff q1 q2 => q1.exec.filter q2.exec.contains
| .select q e => q.exec.filter e.evaluate
| .project q s' subschema => q.exec.map (·.project s' subschema)
| .product q1 q2 _ =>
  q1.exec.flatMap (λ r1 ↦ q2.exec.map (λ r2 ↦ r1.append r2))
| .renameColumn q theCol n' _ => q.exec.map (·.rename theCol)
| .prefixWith q n => q.exec.map (·.prefixWith n)

-- example

#eval disjoint [1,2,3,4] [1,2,3,4]
#eval disjoint [1,2,3,4] [5,6,7,8]

#eval Query.table mountainDiary |>.exec
#eval Query.table mountainDiary |>.union (.table mountainDiary) |>.exec
#eval (Query.table mountainDiary).select tallInUSA |>.exec
#eval Query.table userinfo |>.product (.table mountainDiary) (by decide) |>.exec
#eval Query.table mountainDiary |>.renameColumn .here "diaryName" (by decide) |>.exec
#eval Query.table mountainDiary |>.prefixWith "MountainDiary" |>.exec
#eval
  Query.product
    (Query.table mountainDiary |>.prefixWith "MountainDiary")
    (Query.table waterfallDiary |>.prefixWith "WaterfallDiary")
    (by decide)
  |>.exec
