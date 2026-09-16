import Submission.Spec
open Nat Finset

def term_val (n k : ℕ) : ℤ :=
  let k_int : ℤ := k.cast
  let coeff_a : ℤ := T_coeff k 4 1
  let coeff_b : ℤ := T_coeff k 1 (-1)
  let term_1 := (40 * k_int + 27)
  let term_3_exp : ℕ := n - 1 - k
  let term_3 := ((-6) : ℤ) ^ term_3_exp
  term_1 * term_3 * coeff_a * (coeff_b ^ 2)

def sum_val (n : ℕ) : ℤ := (range n).sum (term_val n)

#eval sum_val 1
#eval sum_val 2
#eval sum_val 3
