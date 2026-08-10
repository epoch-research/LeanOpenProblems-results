import Mathlib

open Nat

theorem solve_7_prime (n : ℕ) (p : ℕ) (hp : p.Prime) (hp_ge11 : p ≥ 11) (hn : n - 5 = p) (hn_ge : n ≥ 16) :
    7 * p ∈ { x : ℕ | x > 0 ∧ (x - 1) % Nat.totient x = n } := by
  simp only [Set.mem_setOf_eq]
  have h_x_pos : 7 * p > 0 := by
    have : p > 0 := hp.pos
    omega
  refine ⟨h_x_pos, ?_⟩
  have h_coprime : Coprime 7 p := by
    have h_p_coprime : Coprime p 7 := by
      rw [hp.coprime_iff_not_dvd]
      intro hdvd
      have hp_le : p ≤ 7 := Nat.le_of_dvd (by decide) hdvd
      omega
    exact h_p_coprime.symm
  have h_tot : Nat.totient (7 * p) = 6 * (p - 1) := by
    rw [Nat.totient_mul h_coprime]
    have : Nat.totient 7 = 6 := by decide
    rw [this, Nat.totient_prime hp]
  rw [h_tot]
  have h_eq : 7 * p - 1 = n + 6 * (p - 1) * 1 := by
    omega
  rw [h_eq]
  rw [Nat.add_mul_mod_self_left]
  have h_lt : n < 6 * (p - 1) := by
    omega
  exact Nat.mod_eq_of_lt h_lt
