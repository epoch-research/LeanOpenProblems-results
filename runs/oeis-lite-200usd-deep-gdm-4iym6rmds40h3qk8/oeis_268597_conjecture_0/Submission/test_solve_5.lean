import Mathlib

open Nat

theorem solve_5_prime (n : ℕ) (p : ℕ) (hp : p.Prime) (hp_ge7 : p ≥ 7) (hn : n - 3 = p) (hn_ge : n ≥ 10) :
    5 * p ∈ { x : ℕ | x > 0 ∧ (x - 1) % Nat.totient x = n } := by
  simp only [Set.mem_setOf_eq]
  have h_x_pos : 5 * p > 0 := by
    have : p > 0 := hp.pos
    omega
  refine ⟨h_x_pos, ?_⟩
  have h_coprime : Coprime 5 p := by
    have h_p_coprime : Coprime p 5 := by
      rw [hp.coprime_iff_not_dvd]
      intro hdvd
      have hp_le : p ≤ 5 := Nat.le_of_dvd (by decide) hdvd
      omega
    exact h_p_coprime.symm
  have h_tot : Nat.totient (5 * p) = 4 * (p - 1) := by
    rw [Nat.totient_mul h_coprime]
    have : Nat.totient 5 = 4 := by decide
    rw [this, Nat.totient_prime hp]
  rw [h_tot]
  have h_eq : 5 * p - 1 = n + 4 * (p - 1) * 1 := by
    omega
  rw [h_eq]
  rw [Nat.add_mul_mod_self_left]
  have h_lt : n < 4 * (p - 1) := by
    omega
  exact Nat.mod_eq_of_lt h_lt
