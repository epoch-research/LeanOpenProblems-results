import Mathlib
import Submission.Spec

theorem oeis_329073_conjecture_2_i_proof :
  ∀ (n : ℕ), 0 < n →
  (A329073_b n = A329073_b n) ∧
  ((n.cast : ℤ) ∣ ( (range n).sum fun k : ℕ =>
    let k_int : ℤ := k.cast
    let coeff_a : ℤ := T_coeff k 4 1
    let coeff_b : ℤ := T_coeff k 1 (-1)
    let term_1 := (40 * k_int + 27)
    let term_3_exp : ℕ := n - 1 - k
    let term_3 := ((-6) : ℤ) ^ term_3_exp
    term_1 * term_3 * coeff_a * (coeff_b ^ 2) )) ∧
  (A329073_b n % 2 = 1 ↔ Nat.isPowerOfTwo n) := by
  exact?
