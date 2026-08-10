import FormalConjectures.Util.ProblemImports

open Nat

lemma test_div (p : ℕ) (hp_gt2 : p > 2) (h_div_lt : (p - 1) / 2 < 2) : p ≤ 4 := by
  have h_div_le : (p - 1) / 2 ≤ 1 := by omega
  have h_mod : (p - 1) % 2 < 2 := Nat.mod_lt (p - 1) (by decide)
  have h_decomp : p - 1 = 2 * ((p - 1) / 2) + (p - 1) % 2 := (Nat.div_add_mod (p - 1) 2).symm
  omega

lemma test_induction_step (n p S p' : ℕ)
    (h_sqrt_eq : sqrt (n + p) = S - 1)
    (h_cond2 : sqrt (n + p) ≥ 12 → p ≤ 4 * sqrt (n + p) - 2)
    (h_eq : sqrt (n + 1 + p') = S - 1)
    (hp'_le : p' ≤ 2 * ((p - 1) / 2)) :
    (sqrt (n + 1 + p') ≥ 12 → p' ≤ 4 * sqrt (n + 1 + p') - 2) := by
  intro hc
  rw [h_eq] at hc
  have hp_le_4S : p ≤ 4 * (S - 1) - 2 := by
    have h_sqrt : sqrt (n + p) = S - 1 := h_sqrt_eq
    have h_cond_premise : sqrt (n + p) ≥ 12 := by omega
    rw [h_sqrt] at h_cond2 h_cond_premise
    exact h_cond2 h_cond_premise
  have h_div : 2 * ((p - 1) / 2) ≤ p - 1 := Nat.mul_div_le (p - 1) 2
  have hp'_le_p_sub_one : p' ≤ p - 1 := le_trans hp'_le h_div
  omega


lemma test_omega_contradiction (n p S_sq p' : ℕ)
    (h_S_sq : S_sq ≥ 196)
    (hsq : n + 1 + p = S_sq)
    (hp_gt2 : p > 2)
    (hp'1 : p' > (p - 1) / 2)
    (hc : p' = 2) :
    n + 1 ≤ 61 := by
  have hp_sub_ge2 : p - 1 ≥ 2 := by omega
  have h_div_le : (p - 1) / 2 ≤ 1 := by omega
  have h_mod : (p - 1) % 2 < 2 := Nat.mod_lt (p - 1) (by decide)
  have h_decomp : p - 1 = 2 * ((p - 1) / 2) + (p - 1) % 2 := (Nat.div_add_mod (p - 1) 2).symm
  have hp_eq : p = p - 1 + 1 := by omega
  omega


