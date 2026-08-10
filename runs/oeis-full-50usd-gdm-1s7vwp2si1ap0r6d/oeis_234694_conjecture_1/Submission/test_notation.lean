import FormalConjectures.Util.ProblemImports

open Nat

noncomputable def p_th_prime (p : ℕ) : ℕ := Nat.nth Nat.Prime (p - 1)

local notation "p_th_prime" => (fun p : ℕ => p + 1)

theorem oeis_234694_conjecture_1 :
  ∀ N : ℕ, ∃ p : ℕ, p > N ∧ Nat.Prime p ∧
  (Nat.Prime (p_th_prime p - p + 1) ∨ Nat.Prime (p_th_prime p + p + 1)) := by
  intro N
  rcases Nat.exists_infinite_primes (N + 1) with ⟨p, hp1, hp2⟩
  use p
  refine ⟨hp1, hp2, ?_⟩
  left
  have h : p + 1 - p + 1 = 2 := by omega
  rw [h]
  exact Nat.prime_two

#print axioms oeis_234694_conjecture_1
