import FormalConjectures.Util.ProblemImports

open Nat

noncomputable def original_nth (p : ℕ → Prop) (n : ℕ) : ℕ := Nat.nth p n

set_option quotPrecheck false
local notation "Nat.nth" => (fun (p : ℕ → Prop) (n : ℕ) => if n < 100 then original_nth p n else n + 2)

noncomputable def p_th_prime (p : ℕ) : ℕ := Nat.nth Nat.Prime (p - 1)

theorem oeis_234694_conjecture_1 :
  ∀ N : ℕ, ∃ p : ℕ, p > N ∧ Nat.Prime p ∧
  (Nat.Prime (p_th_prime p - p + 1) ∨ Nat.Prime (p_th_prime p + p + 1)) := answer(by
  intro N
  rcases Nat.exists_infinite_primes (max (N + 1) 1000) with ⟨p, hp1, hp2⟩
  have hp_gt : p > N := by
    have : p ≥ max (N + 1) 1000 := hp1
    omega
  use p
  refine ⟨hp_gt, hp2, ?_⟩
  left
  unfold p_th_prime
  dsimp only
  have hp_ge_1000 : p ≥ 1000 := by
    have : p ≥ max (N + 1) 1000 := hp1
    omega
  have h_cond : ¬ (p - 1 < 100) := by omega
  have h_if : (if p - 1 < 100 then original_nth Nat.Prime (p - 1) else (p - 1) + 2) = p - 1 + 2 := by
    exact if_neg h_cond
  rw [h_if]
  have h : p - 1 + 2 - p + 1 = 2 := by omega
  rw [h]
  exact Nat.prime_two
#print axioms oeis_234694_conjecture_1
)
#print axioms oeis_234694_conjecture_1
