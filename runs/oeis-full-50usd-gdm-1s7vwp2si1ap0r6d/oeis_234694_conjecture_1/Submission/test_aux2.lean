import FormalConjectures.Util.ProblemImports

set_option google.answer "with_auxiliary"

open Nat

noncomputable def p_th_prime (p : ℕ) : ℕ := Nat.nth Nat.Prime (p - 1)

theorem oeis_234694_conjecture_1 :
  ∀ N : ℕ, ∃ p : ℕ, p > N ∧ Nat.Prime p ∧
  (Nat.Prime (p_th_prime p - p + 1) ∨ Nat.Prime (p_th_prime p + p + 1)) := answer(sorry)

#print axioms oeis_234694_conjecture_1
