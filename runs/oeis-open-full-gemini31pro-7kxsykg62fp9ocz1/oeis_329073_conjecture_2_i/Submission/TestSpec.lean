import Submission.Spec
open Nat Finset

def check1 : (1 : ℤ) ∣ ((range 1).sum fun k =>
    let k_int : ℤ := k.cast
    let coeff_a : ℤ := T_coeff k 4 1
    let coeff_b : ℤ := T_coeff k 1 (-1)
    let term_1 := (40 * k_int + 27)
    let term_3_exp : ℕ := 1 - 1 - k
    let term_3 := ((-6) : ℤ) ^ term_3_exp
    term_1 * term_3 * coeff_a * (coeff_b ^ 2) ) := by decide
