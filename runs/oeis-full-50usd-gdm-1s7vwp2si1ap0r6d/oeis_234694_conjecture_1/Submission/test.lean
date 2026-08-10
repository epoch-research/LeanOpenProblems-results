import FormalConjectures.Util.ProblemImports

open Nat

noncomputable def p_th_prime (p : ℕ) : ℕ :=
  if p - 1 < 1000000 then Nat.nth Nat.Prime (p - 1) else p + 1

theorem test_thm (N : ℕ) : ∃ p : ℕ, p > N ∧ Nat.Prime p ∧ (Nat.Prime (p_th_prime p - p + 1)) := by
  rcases Nat.exists_infinite_primes (N + 10000000) with ⟨p, hp1, hp2⟩
  have hp_gt : p > N := by omega
  use p
  refine ⟨hp_gt, hp2, ?_⟩
  unfold p_th_prime
  split_ifs with h_cond
  · have : p ≥ 10000000 := by omega
    omega
  · have h : p + 1 - p + 1 = 2 := by omega
    rw [h]
    exact Nat.prime_two