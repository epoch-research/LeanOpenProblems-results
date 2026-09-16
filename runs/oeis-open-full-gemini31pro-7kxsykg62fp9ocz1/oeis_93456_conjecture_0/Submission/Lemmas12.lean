import Mathlib

open Nat Finset

lemma n_choose_two_div (n : ℕ) (hn : 1 ≤ n) : (2 : ℤ) * ((n * (n - 1) / 2 : ℕ) : ℤ) = ((n : ℕ) : ℤ) * (((n : ℕ) : ℤ) - 1) := sorry

lemma h_R2_proof (p M n : ℕ) (hL1_val_eq : n * (n - 1) / 2 = p * M) (hn_gt0 : 1 ≤ n) :
  (n + 1).choose 2 = p * M + n := by
  have H_choose : (n + 1).choose 2 = (n + 1) * n / 2 := by
    have : n + 1 - 1 = n := by omega
    rw [Nat.choose_two_right, this]
  have H_z : (((n + 1) * n / 2 : ℕ) : ℤ) = (p * M + n : ℤ) := by
    have H_n : (((n + 1) * n / 2 : ℕ) : ℤ) = ((n * (n - 1) / 2 : ℕ) : ℤ) + n := by
      have h1 : (2:ℤ) * (((n+1)*n / 2 : ℕ):ℤ) = (n+1:ℤ)*n := by
        have H_div := n_choose_two_div (n+1) (by omega)
        have H_sub : (((n + 1 : ℕ) : ℤ) - 1) = (n : ℤ) := by omega
        rw [H_sub] at H_div
        exact H_div
      have h2 : (2:ℤ) * ((n * (n-1) / 2 : ℕ):ℤ) = (n:ℤ)*((n:ℤ)-1) := by
        have := n_choose_two_div n hn_gt0
        exact this
      have H3 : (2:ℤ) * (((n + 1) * n / 2 : ℕ) : ℤ) = (2:ℤ) * (((n * (n - 1) / 2 : ℕ) : ℤ) + n) := by
        calc (2:ℤ) * (((n + 1) * n / 2 : ℕ) : ℤ) = (n+1:ℤ)*n := h1
        _ = (n:ℤ)*((n:ℤ)-1) + 2*(n:ℤ) := by ring
        _ = (2:ℤ) * ((n * (n-1) / 2 : ℕ):ℤ) + 2*(n:ℤ) := by rw [h2]
        _ = (2:ℤ) * (((n * (n - 1) / 2 : ℕ) : ℤ) + n) := by ring
      have h_two : (2:ℤ) ≠ 0 := by decide
      exact mul_left_cancel₀ h_two H3
    have H_M : ((n * (n - 1) / 2 : ℕ) : ℤ) = p * M := by exact_mod_cast hL1_val_eq
    rw [H_M] at H_n
    exact H_n
  rw [H_choose]
  exact_mod_cast H_z

