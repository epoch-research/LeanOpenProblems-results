import FormalConjectures.Util.ProblemImports
open Nat Finset

example : Nat.choose 4 2 = 6 := by norm_num [Nat.choose]
example : Nat.choose 5 2 = 10 := by norm_num [Nat.choose]
example : Nat.choose 6 3 = 20 := by norm_num [Nat.choose]
example : Nat.choose 4 2 = 6 := by
  rw [Nat.choose_eq_factorial_div_factorial (by omega : 2 ≤ 4)]
  norm_num
example : Nat.choose 6 3 = 20 := by
  rw [Nat.choose_eq_factorial_div_factorial (by omega : 3 ≤ 6)]
  norm_num

example : (Nat.choose 4 2)^2 * (Nat.choose 5 2) = 360 := by
  rw [Nat.choose_eq_factorial_div_factorial (by omega : 2 ≤ 4)]
  rw [Nat.choose_eq_factorial_div_factorial (by omega : 2 ≤ 5)]
  norm_num
