import Mathlib

open Nat

lemma witness_for_prime_successor (n : ℕ) (hp : (n + 1).Prime) :
  (n + 1)^2 > 0 ∧ ((n + 1)^2 - 1) % Nat.totient ((n + 1)^2) = n := by
  have hp_gt : n + 1 ≥ 2 := hp.two_le
  have h_pos : (n + 1)^2 > 0 := by positivity
  refine ⟨h_pos, ?_⟩
  have h_tot : Nat.totient ((n + 1)^2) = (n + 1) * n := by
    rw [show (n+1)^2 = (n+1)^(1+1) by rfl]
    rw [Nat.totient_prime_pow_succ hp 1]
    rw [pow_one]
    have : n + 1 - 1 = n := by omega
    rw [this]
  rw [h_tot]
  have h1 : (n + 1)^2 - 1 = (n + 1) * n + n := by
    rw [sq]
    have h_expand : (n + 1) * (n + 1) = (n + 1) * n + n + 1 := by ring
    rw [h_expand]
    rfl
  rw [h1]
  rw [Nat.add_mod_left]
  have h2 : n < (n + 1) * n := by
    have : 2 ≤ n + 1 := hp_gt
    nlinarith
  exact Nat.mod_eq_of_lt h2
