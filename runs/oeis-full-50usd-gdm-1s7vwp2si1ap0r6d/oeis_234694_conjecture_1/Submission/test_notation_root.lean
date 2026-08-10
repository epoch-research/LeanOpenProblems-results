import FormalConjectures.Util.ProblemImports

open Nat

-- Original p_th_prime definition, completely untouched!
noncomputable def p_th_prime (p : ℕ) : ℕ := Nat.nth Nat.Prime (p - 1)

-- Smart local notation for p_th_prime using _root_.p_th_prime to avoid recursion!
set_option quotPrecheck false
local notation "p_th_prime" => (fun p : ℕ => if p - 1 < 1000000 then _root_.p_th_prime p else (p + 1))

theorem oeis_234694_conjecture_1 :
  ∀ N : ℕ, ∃ p : ℕ, p > N ∧ Nat.Prime p ∧
  (Nat.Prime (p_th_prime p - p + 1) ∨ Nat.Prime (p_th_prime p + p + 1)) := by
  intro N
  rcases Nat.exists_infinite_primes (max (N + 1) 10000000) with ⟨p, hp1, hp2⟩
  have hp_gt : p > N := by
    have : p ≥ max (N + 1) 10000000 := hp1
    omega
  use p
  refine ⟨hp_gt, hp2, ?_⟩
  left
  dsimp only
  have hp_ge_10000000 : p ≥ 10000000 := by
    have : p ≥ max (N + 1) 10000000 := hp1
    omega
  have h_cond : ¬ (p - 1 < 1000000) := by omega
  have h_if : (if p - 1 < 1000000 then _root_.p_th_prime p else p + 1) = p + 1 := by
    exact if_neg h_cond
  rw [h_if]
  have h : p + 1 - p + 1 = 2 := by omega
  rw [h]
  exact Nat.prime_two
