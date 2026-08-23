import FormalConjectures.Util.ProblemImports

open Nat

example : sqrt 49 = 7 := rfl
example : 7 * 7 = 49 := rfl
example : sqrt 57 = 7 := rfl
example : 7 * 7 ≠ 57 := by decide

-- large
example : sqrt (8 * 100000000003 + 1) * sqrt (8 * 100000000003 + 1) ≠ 8 * 100000000003 + 1 := by
  decide

def bitOddSq (t : ℕ) : ℕ :=
  let s := sqrt t
  (if s * s = t then 1 else 0) * (s % 2)

#eval bitOddSq 49
#eval bitOddSq 57
#eval bitOddSq (8*6+1)
