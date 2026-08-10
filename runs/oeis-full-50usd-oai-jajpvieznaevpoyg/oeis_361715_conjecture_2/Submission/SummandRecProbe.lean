import FormalConjectures.Util.ProblemImports
open Nat Finset

def a (n : ℕ) : ℕ :=
  ∑ k ∈ range n, (n.choose k) ^ 2 * multichoose n k

def term (n k : ℕ) : ℕ := (n.choose k)^2 * multichoose n k

#check Nat.choose_succ_succ
#check Nat.choose_eq_factorial_div_factorial
#check Nat.choose_mul_succ_eq
#check Nat.succ_mul_choose_eq
#check Nat.choose_eq_zero_of_lt
#check Nat.multichoose_eq

example : term 4 0 = 1 := by norm_num [term, Nat.multichoose_eq]
example : term 4 1 = 64 := by norm_num [term, Nat.multichoose_eq]
example : term 4 2 = 360 := by norm_num [term, Nat.multichoose_eq]
example : term 4 3 = 320 := by norm_num [term, Nat.multichoose_eq]
example : a 4 = 745 := by
  rw [a]
  norm_num [Nat.multichoose_eq]
