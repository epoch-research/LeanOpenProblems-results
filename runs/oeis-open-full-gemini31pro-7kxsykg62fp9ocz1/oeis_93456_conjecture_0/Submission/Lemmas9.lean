import Mathlib

open Nat Finset

lemma n_choose_two_div (n : ℕ) (hn : 1 ≤ n) : (2 : ℤ) * ((n * (n - 1) / 2 : ℕ) : ℤ) = ((n : ℕ) : ℤ) * (((n : ℕ) : ℤ) - 1) := by
  have H1 : 2 ∣ n * (n - 1) := Even.two_dvd (Nat.even_mul_pred_self n)
  have H2 : 2 * (n * (n - 1) / 2) = n * (n - 1) := Nat.mul_div_cancel' H1
  have H3 : (2 : ℤ) * ((n * (n - 1) / 2 : ℕ) : ℤ) = ((n * (n - 1) : ℕ) : ℤ) := by exact_mod_cast H2
  have H4 : ((n * (n - 1) : ℕ) : ℤ) = (n : ℤ) * ((n : ℤ) - 1) := by
    rw [Nat.cast_mul, Nat.cast_sub hn]
    rfl
  rw [H4] at H3
  exact H3

lemma hL1_val_eq (p M : ℕ) (hp : 5 ≤ p) (hM_ge : p ≤ M) :
  p * (p - 2) * (p * (p - 2) - 1) / 2 = p * M ↔
  p * (p * p - 4 * p + 3) + 2 = 2 * M := by
  have hp2 : 2 ≤ p := by omega
  have H1 : (2 : ℤ) * ((p * (p - 2) * (p * (p - 2) - 1) / 2 : ℕ) : ℤ) = ((p * (p - 2) : ℕ) : ℤ) * (((p * (p - 2) : ℕ) : ℤ) - 1) := by
    have hn : 1 ≤ p * (p - 2) := by
      have : 3 ≤ p - 2 := by omega
      nlinarith
    exact n_choose_two_div (p * (p - 2)) hn
  have H2 : ((p * (p - 2) : ℕ) : ℤ) = (p : ℤ) * ((p : ℤ) - 2) := by
    rw [Nat.cast_mul, Nat.cast_sub hp2]
    rfl
  have H3 : ((p * (p - 2) : ℕ) : ℤ) * (((p * (p - 2) : ℕ) : ℤ) - 1) = (p : ℤ) * ((p : ℤ) * (p : ℤ) - 4 * (p : ℤ) + 3) * (p : ℤ) + 2 * (p : ℤ) := by
    rw [H2]
    ring
  rw [H3] at H1
  constructor
  · intro h
    have : ((p * M : ℕ) : ℤ) = ((p * (p - 2) * (p * (p - 2) - 1) / 2 : ℕ) : ℤ) := by exact_mod_cast h.symm
    have h1 : (2 : ℤ) * ((p * M : ℕ) : ℤ) = (2 : ℤ) * (p : ℤ) * (M : ℤ) := by push_cast; ring
    have h2 : (2 : ℤ) * (p : ℤ) * (M : ℤ) = (p : ℤ) * ((p : ℤ) * (p : ℤ) - 4 * (p : ℤ) + 3) * (p : ℤ) + 2 * (p : ℤ) := by
      nlinarith
    have hp_pos : (p : ℤ) ≠ 0 := by omega
    have : (p : ℤ) * (2 * (M : ℤ)) = (p : ℤ) * ((p : ℤ) * ((p : ℤ) * (p : ℤ) - 4 * (p : ℤ) + 3) + 2) := by
      calc (p : ℤ) * (2 * (M : ℤ)) = (2 : ℤ) * (p : ℤ) * (M : ℤ) := by ring
      _ = (p : ℤ) * ((p : ℤ) * (p : ℤ) - 4 * (p : ℤ) + 3) * (p : ℤ) + 2 * (p : ℤ) := h2
      _ = (p : ℤ) * ((p : ℤ) * ((p : ℤ) * (p : ℤ) - 4 * (p : ℤ) + 3) + 2) := by ring
    have h_final : 2 * (M : ℤ) = (p : ℤ) * ((p : ℤ) * (p : ℤ) - 4 * (p : ℤ) + 3) + 2 := by
      exact mul_left_cancel₀ hp_pos this
    have h_cast : ((p * (p * p - 4 * p + 3) + 2 : ℕ) : ℤ) = (p : ℤ) * ((p : ℤ) * (p : ℤ) - 4 * (p : ℤ) + 3) + 2 := by
      have hp4 : 4 * p ≤ p * p := by
        have : 4 * 5 ≤ p * p := by nlinarith
        nlinarith
      push_cast [Nat.cast_sub hp4]
      ring
    rw [← h_cast] at h_final
    have h_final2 : ((p * (p * p - 4 * p + 3) + 2 : ℕ) : ℤ) = ((2 * M : ℕ) : ℤ) := by
      push_cast
      exact h_final.symm
    exact_mod_cast h_final2
  · intro h
    have h_cast : ((p * (p * p - 4 * p + 3) + 2 : ℕ) : ℤ) = (p : ℤ) * ((p : ℤ) * (p : ℤ) - 4 * (p : ℤ) + 3) + 2 := by
      have hp4 : 4 * p ≤ p * p := by
        have : 4 * 5 ≤ p * p := by nlinarith
        nlinarith
      push_cast [Nat.cast_sub hp4]
      ring
    have h_final : (p : ℤ) * ((p : ℤ) * (p : ℤ) - 4 * (p : ℤ) + 3) + 2 = 2 * (M : ℤ) := by
      rw [← h_cast]
      exact_mod_cast h
    have : (2 : ℤ) * ((p * M : ℕ) : ℤ) = (2 : ℤ) * ((p * (p - 2) * (p * (p - 2) - 1) / 2 : ℕ) : ℤ) := by
      calc (2 : ℤ) * ((p * M : ℕ) : ℤ) = (p : ℤ) * (2 * (M : ℤ)) := by push_cast; ring
      _ = (p : ℤ) * ((p : ℤ) * ((p : ℤ) * (p : ℤ) - 4 * (p : ℤ) + 3) + 2) := by rw [← h_final]
      _ = (p : ℤ) * ((p : ℤ) * (p : ℤ) - 4 * (p : ℤ) + 3) * (p : ℤ) + 2 * (p : ℤ) := by ring
      _ = (2 : ℤ) * ((p * (p - 2) * (p * (p - 2) - 1) / 2 : ℕ) : ℤ) := H1.symm
    have : ((p * M : ℕ) : ℤ) = ((p * (p - 2) * (p * (p - 2) - 1) / 2 : ℕ) : ℤ) := by
      have h2 : (2 : ℤ) ≠ 0 := by decide
      exact mul_left_cancel₀ h2 this
    exact_mod_cast this.symm
