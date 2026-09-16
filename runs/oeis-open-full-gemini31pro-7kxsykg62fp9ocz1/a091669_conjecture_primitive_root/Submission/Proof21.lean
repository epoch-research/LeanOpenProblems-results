import Mathlib
import Submission.Spec
import Submission.Proof6

open Nat

lemma vp_fact_upper_bound_2 (n : ℕ) (hn2 : n > 2) (heven : 2 ∣ n) :
  padicValNat 2 (n - 1).factorial < n - 2 := by
  have h1 : padicValNat 2 (n - 1).factorial = (n - 1) - (Nat.digits 2 (n - 1)).sum := by
    have h_sub : (2 - 1) * padicValNat 2 (n - 1).factorial = (n - 1) - (Nat.digits 2 (n - 1)).sum := by
      exact sub_one_mul_padicValNat_factorial (n - 1)
    have h_sub2 : 2 - 1 = 1 := rfl
    rw [h_sub2, one_mul] at h_sub
    exact h_sub
  have h2 : (Nat.digits 2 (n - 1)).sum ≥ 2 := by
    rcases heven with ⟨m, hm⟩
    have hm2 : m ≥ 2 := by omega
    have hn1 : n - 1 = 1 + 2 * (m - 1) := by omega
    have hb : 1 < 2 := by omega
    have hxb : 1 < 2 := by omega
    have hxy : 1 ≠ 0 ∨ m - 1 ≠ 0 := Or.inl (by omega)
    have h_digits : Nat.digits 2 (n - 1) = 1 :: Nat.digits 2 (m - 1) := by
      rw [hn1]
      exact Nat.digits_add 2 hb 1 (m - 1) hxb hxy
    have h_sum : (Nat.digits 2 (n - 1)).sum = 1 + (Nat.digits 2 (m - 1)).sum := by
      rw [h_digits, List.sum_cons]
    have hm1_pos : m - 1 > 0 := by omega
    have h_sum_m1 : (Nat.digits 2 (m - 1)).sum ≥ 1 := digits_sum_pos 2 (m - 1) hb hm1_pos
    omega
  omega
