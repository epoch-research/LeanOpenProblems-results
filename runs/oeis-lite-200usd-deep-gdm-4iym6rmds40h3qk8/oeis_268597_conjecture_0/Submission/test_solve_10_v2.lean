import Mathlib

open Nat

theorem solve_10_prime (n : ℕ) (q : ℕ) (hq : q.Prime) (hq_ge7 : q ≥ 7) (hn : n = 2 * q + 7) :
    10 * q ∈ { x : ℕ | x > 0 ∧ (x - 1) % Nat.totient x = n } := by
  simp only [Set.mem_setOf_eq]
  have h_x_pos : 10 * q > 0 := by
    have : q > 0 := hq.pos
    omega
  refine ⟨h_x_pos, ?_⟩
  have h_coprime2 : Coprime 2 q := by
    have : Coprime q 2 := by
      rw [hq.coprime_iff_not_dvd]
      intro hdvd
      have hq2 : q ≤ 2 := Nat.le_of_dvd (by decide) hdvd
      omega
    exact this.symm
  have h_coprime5 : Coprime 5 q := by
    have : Coprime q 5 := by
      rw [hq.coprime_iff_not_dvd]
      intro hdvd
      have hq5 : q ≤ 5 := Nat.le_of_dvd (by decide) hdvd
      omega
    exact this.symm
  have h_coprime : Coprime 10 q := by
    have h_eq : 10 = 2 * 5 := by decide
    rw [h_eq]
    exact Coprime.mul_left h_coprime2 h_coprime5
  have h_tot : Nat.totient (10 * q) = 4 * (q - 1) := by
    rw [Nat.totient_mul h_coprime]
    have : Nat.totient 10 = 4 := by decide
    rw [this, Nat.totient_prime hq]
  rw [h_tot]
  have h_eq : 10 * q - 1 = n + 4 * (q - 1) * 2 := by
    omega
  rw [h_eq]
  rw [Nat.add_mul_mod_self_left]
  have h_lt : n < 4 * (q - 1) := by
    omega
  exact Nat.mod_eq_of_lt h_lt
