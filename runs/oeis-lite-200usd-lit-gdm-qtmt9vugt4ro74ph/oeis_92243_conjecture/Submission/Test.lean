import FormalConjectures.Util.ProblemImports

open Nat BigOperators Int

lemma nth_prime_le_two_mul (k : ℕ) : Nat.nth Nat.Prime (k + 1) ≤ 2 * Nat.nth Nat.Prime k := by
  have hp_k : Nat.Prime (Nat.nth Nat.Prime k) := Nat.nth_mem_of_infinite Nat.infinite_setOf_prime k
  have hk0 : Nat.nth Nat.Prime k ≠ 0 := by
    have := Nat.Prime.two_le hp_k
    omega
  obtain ⟨p, hp, hlt, hle⟩ := Nat.exists_prime_lt_and_le_two_mul (Nat.nth Nat.Prime k) hk0
  have hp_eq : p = Nat.nth Nat.Prime (Nat.count Nat.Prime p) := (Nat.nth_count hp).symm
  have h_lt_nth : Nat.nth Nat.Prime k < Nat.nth Nat.Prime (Nat.count Nat.Prime p) := by
    rw [← hp_eq]
    exact hlt
  rw [Nat.nth_lt_nth Nat.infinite_setOf_prime] at h_lt_nth
  have h_le_count : k + 1 ≤ Nat.count Nat.Prime p := h_lt_nth
  have h_le_nth : Nat.nth Nat.Prime (k + 1) ≤ Nat.nth Nat.Prime (Nat.count Nat.Prime p) := by
    rwa [Nat.nth_le_nth Nat.infinite_setOf_prime]
  rw [← hp_eq] at h_le_nth
  omega

lemma nth_prime_le_pow (k : ℕ) (hk : k ≥ 3) : Nat.nth Nat.Prime k ≤ 2^k := by
  induction k, hk using Nat.le_induction with
  | base =>
    have h_eq : Nat.nth Nat.Prime 3 = 7 := Nat.nth_prime_three_eq_seven
    omega
  | succ k hk ih =>
    have h_le := nth_prime_le_two_mul k
    have h_pow : 2^(k + 1) = 2^k * 2 := rfl
    omega
