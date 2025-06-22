def maxDay
: Nat → Nat → Nat
| year, month =>
  match month with
  | 1 | 3 | 5 | 7 | 8 | 10 | 12 => 31
  | 4 | 6 | 9 | 11 => 30
  | 2 => if isLeepYear year then 29 else 28
  | _ => default
where
  isLeepYear : Nat → Bool
  | year => (year % 4 = 0 ∧ year % 100 ≠ 0) ∨ year % 400 = 0

structure Date : Type where
  year : Nat
  month : Nat
  day : Nat
  month_valid : 0 < month ∧ month ≤ 12
  day_valid : 0 < day ∧ day ≤ maxDay year month

-- instance

instance : Repr Date where
  reprPrec date _nat :=
    if date.month < 10
      then s!"{date.year}/0{date.month}/{date.day}"
      else s!"{date.year}/{date.month}/{date.day}"

def Date.beq
: Date → Date → Bool
| date₁, date₂
  => date₁.year == date₂.year
  ∧ date₁.month == date₂.month
  ∧ date₁.day == date₂.day
instance : BEq Date where
  beq := Date.beq

-- other

macro "date!" "(" year:term "," month:term "," day:term ")" : term =>
  `(Date.mk $year $month $day (by simp) (by decide))

-- example

example := Date.mk 2024 2 29 (by simp) (by decide)
#eval Date.mk 2024 12 31 (by simp) (by decide)
#eval date!(2024, 02, 29)
