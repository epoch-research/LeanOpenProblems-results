import Mathlib
import Submission.Spec
open Finset

lemma even_not_match {n : ℕ} (hn : 1 < n) (hn_even : Even n) : ¬ (n * n ≡ 1 [MOD A000224 n * (A000224 n - 1)]) := by
  intro h
  have H1 : 2 ∣ A000224 n * (A000224 n - 1) := by
    have h_or : 2 ∣ A000224 n ∨ 2 ∣ A000224 n - 1 := by
      by_cases h2 : A000224 n % 2 = 0
      · exact Or.inl (Nat.dvd_of_mod_eq_zero h2)
      · exact Or.inr ⟨A000224 n / 2, by omega⟩
    cases h_or with
    | inl h_dvd =>
      obtain ⟨x, hx⟩ := h_dvd
      exact ⟨x * (A000224 n - 1), by rw [hx]; ring⟩
    | inr h_dvd =>
      obtain ⟨x, hx⟩ := h_dvd
      exact ⟨A000224 n * x, by rw [hx]; ring⟩
  have H2 : A000224 n * (A000224 n - 1) ∣ n * n - 1 := by
    have h_pos : 1 ≤ n * n := by nlinarith
    exact (Nat.modEq_iff_dvd' h_pos).mp h.symm
  have H3 : 2 ∣ n * n - 1 := dvd_trans H1 H2
  have H4 : (n * n - 1) % 2 = 0 := Nat.mod_eq_zero_of_dvd H3
  obtain ⟨k, hk⟩ := hn_even
  have H5 : (n * n) % 2 = 0 := by
    rw [hk]
    have : (k + k) * (k + k) = 2 * (2 * k * k) := by ring
    rw [this]
    exact Nat.mul_mod_right 2 _
  have H6 : (n * n - 1) % 2 = 1 := by
    have h_n2 : 1 ≤ n * n := by nlinarith
    have h_eq : n * n = 2 * (n * n / 2) := by
      exact Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero H5) |>.symm
    have h_pos : 1 ≤ n * n / 2 := by omega
    have h_eq2 : n * n - 1 = 1 + 2 * (n * n / 2 - 1) := by omega
    rw [h_eq2]
    have H_mod := Nat.add_mul_mod_self_left 1 2 (n * n / 2 - 1)
    exact H_mod
  rw [H6] at H4
  contradiction
