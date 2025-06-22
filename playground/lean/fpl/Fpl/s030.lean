/-
Prove the following theorems using `rfl`: `2 + 3 = 5`, `15 - 8 = 7`,
`"Hello, ".append "world" = "Hello, world"`. What happens if `rfl` is used to
prove `5 < 18`? Why?
-/

example : 2 + 3 = 5 := by rfl
example : 15 - 8 = 7 := by rfl
example : "Hello, ".append "world" = "Hello, world" := by rfl
-- example : 5 < 18 := by rfl

/-
Prove the following theorems using `by simp`: `2 + 3 = 5`, `15 - 8 = 7`,
`"Hello, ".append "world" = "Hello, world"`, `5 < 18`.
-/

example : 2 + 3 = 5 := by simp
example : 15 - 8 = 7 := by simp
-- example : "Hello, ".append "world" = "Hello, world" := by simp
example : 5 < 18 := by simp

/-
Write a function that looks up the fifth entry in a list. Pass the evidence that
this lookup is safe as an argument to the function.
-/

def lookup6th (list : List α) (ok : list.length > 6) : α :=
  list[6]
#check lookup6th
#eval lookup6th [1, 2, 3, 4, 5, 6, 7] (by simp)

def lookup5th : (list : List α) → list.length > 5 → α
| list, h => list[5]'h
#check lookup5th
#eval lookup5th [1, 2, 3, 4, 5, 6] (by simp)

-- def lookup50th : List α → Option α
-- | list => list[50]?
