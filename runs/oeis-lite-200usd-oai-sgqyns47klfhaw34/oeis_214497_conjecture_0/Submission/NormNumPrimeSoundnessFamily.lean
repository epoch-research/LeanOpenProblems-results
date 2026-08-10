import FormalConjectures.Util.ProblemImports
open Nat

-- Known composites should not be provable prime by norm_num.
example : ¬ Nat.Prime 1 := by norm_num
example : ¬ Nat.Prime 4 := by norm_num
example : ¬ Nat.Prime 9 := by norm_num
example : ¬ Nat.Prime 15 := by norm_num
example : ¬ Nat.Prime 21 := by norm_num

-- Some family non-witness values are composite/nonprime; make sure no accidental proof.
example : ¬ (Nat.Prime ((3 ^ 1 - 0) * (2 ^ 1) - 1) ∧ Nat.Prime ((3 ^ 1 - 0) * (2 ^ 1) + 1)) := by norm_num
example : ¬ (Nat.Prime ((3 ^ 2 - 0) * (2 ^ 2) - 1) ∧ Nat.Prime ((3 ^ 2 - 0) * (2 ^ 2) + 1)) := by norm_num
example : (Nat.Prime ((3 ^ 1 - 1) * (2 ^ 1) - 1) ∧ Nat.Prime ((3 ^ 1 - 1) * (2 ^ 1) + 1)) := by norm_num
