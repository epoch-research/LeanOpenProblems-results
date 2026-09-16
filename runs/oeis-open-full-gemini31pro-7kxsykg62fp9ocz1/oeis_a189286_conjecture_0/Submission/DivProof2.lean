import Mathlib

open Nat

lemma padicValNat_mul_eq (a b p : ℕ) (hp : p.Prime) (ha : a > 0) (hb : b > 0) :
  padicValNat p (a * b) = padicValNat p a + padicValNat p b := by
  have h1 : (a * b).factorization p = a.factorization p + b.factorization p := by
    rw [Nat.factorization_mul (by omega) (by omega), Finsupp.coe_add, Pi.add_apply]
  rw [← factorization_def _ hp, ← factorization_def _ hp, ← factorization_def _ hp]
  exact h1

lemma choose_mul (a b c : ℕ) (h1 : b + c = a) :
  a.choose b * b.factorial * c.factorial = a.factorial := by
  have : c = a - b := by omega
  rw [this]
  have h_le : b ≤ a := by omega
  exact choose_mul_factorial_mul_factorial h_le

lemma T_mul (k : ℕ) :
  ((6 * k).choose (3 * k) * (3 * k).choose k) * k.factorial * (2 * k).factorial * (3 * k).factorial = (6 * k).factorial := by
  have h1 : (3 * k).choose k * k.factorial * (2 * k).factorial = (3 * k).factorial := choose_mul _ _ _ (by omega)
  calc
    ((6 * k).choose (3 * k) * (3 * k).choose k) * k.factorial * (2 * k).factorial * (3 * k).factorial
      = (6 * k).choose (3 * k) * ((3 * k).choose k * k.factorial * (2 * k).factorial) * (3 * k).factorial := by ring
    _ = (6 * k).choose (3 * k) * (3 * k).factorial * (3 * k).factorial := by rw [h1]
    _ = (6 * k).factorial := choose_mul _ _ _ (by omega)

lemma p_val_T (k p b : ℕ) (hp : p.Prime) (hb : log p (6 * k) < b) :
  padicValNat p ((6 * k).choose (3 * k) * (3 * k).choose k) =
  ∑ i ∈ Finset.Ico 1 b, (6 * k / p ^ i - 3 * k / p ^ i - 2 * k / p ^ i - k / p ^ i) := by
  sorry

