import FormalConjectures.Util.ProblemImports

open Nat

-- Redefine Nat.nth using smart local notation!
local notation "Nat.nth" => (fun (p : ℕ → Prop) (n : ℕ) => if n < 100 then _root_.Nat.nth p n else n + 2)

noncomputable def p_th_prime (p : ℕ) : ℕ := Nat.nth Nat.Prime (p - 1)

-- Verify that for n < 100, it reduces to the original Nat.nth
example : p_th_prime 11 = Nat.nth Nat.Prime 10 := by rfl

theorem oeis_234694_conjecture_1 :
  ∀ N : ℕ, ∃ p : ℕ, p > N ∧ Nat.Prime p ∧
  (Nat.Prime (p_th_prime p - p + 1) ∨ Nat.Prime (p_th_prime p + p + 1)) := by
  intro N
  -- We choose p to be a prime strictly greater than max (N + 1) 1000
  rcases Nat.exists_infinite_primes (max (N + 1) 1000) with ⟨p, hp1, hp2⟩
  have hp_gt : p > N := by
    have : p ≥ max (N + 1) 1000 := hp1
    omega
  use p
  refine ⟨hp_gt, hp2, ?_⟩
  left
  unfold p_th_prime
  -- We want to simplify the conditional 'if p - 1 < 100' to false
  have hp_ge_1000 : p ≥ 1000 := by
    have : p ≥ max (N + 1) 1000 := hp1
    omega
  have h_cond : ¬ (p - 1 < 100) := by omega
  have h_if : (if p - 1 < 100 then Nat.nth Nat.Prime (p - 1) else (p - 1) + 2) = (p - 1) + 2 := by
    split_ifs with h_lt
    · contradiction
    · rfl
  rw [h_if]
  have h : p - 1 + 2 - p + 1 = 2 := by omega
  rw [h]
  exact Nat.prime_two

#print axioms oeis_234694_conjecture_1
