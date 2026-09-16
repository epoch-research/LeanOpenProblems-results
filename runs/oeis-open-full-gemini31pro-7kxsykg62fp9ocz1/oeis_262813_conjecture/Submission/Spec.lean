import FormalConjectures.Util.ProblemImports

open Finset Nat

def triangular (z : ℕ) : ℕ := z * (z + 1) / 2

def a (n : ℕ) : ℕ :=
  (range (n + 1)).sum fun x =>
  (range (n + 1)).sum fun y =>
  (range (n + 1)).sum fun z =>
    if z > 0 ∧ x^3 + y^2 + triangular z = n then 1 else 0

theorem oeis_262813_conjecture :
  let S : Finset ℕ := {1, 9, 21, 35, 98, 152, 306}
  ∀ n : ℕ, n > 0 → (a n > 0 ∧ (a n = 1 ↔ n ∈ S)) := by
  sorry

theorem oeis_262813_conjecture.disproof : ¬ (type_of% @oeis_262813_conjecture) := by
  intro h
  have hc := h 510 (by decide)
  sorry
