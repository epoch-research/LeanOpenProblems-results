import FormalConjectures.Util.ProblemImports

open Nat

/--
A273917: Number of ordered ways to write $n$ as $w^2 + 3x^2 + y^4 + z^5$, where $w$ is a positive integer and $x,y,z$ are nonnegative integers.
-/
def a (n : ℕ) : ℕ :=
  (Finset.range (n + 1)).sum fun w =>
  (Finset.range (n + 1)).sum fun x =>
  (Finset.range (n + 1)).sum fun y =>
  (Finset.range (n + 1)).sum fun z =>
    if w > 0 ∧ w^2 + 3 * x^2 + y^4 + z^5 = n then 1 else 0

theorem oeis_a273917_conjecture_i (n : ℕ) (hn : n > 0) : a n > 0 := sorry

theorem oeis_a273917_conjecture_i.disproof : ¬ (type_of% @oeis_a273917_conjecture_i) := fun h => 
  have h1 : a 6 > 0 := h 6 (by decide)
  have h2 : a 6 = 2 := rfl
  have h3 : (2:ℕ) > 0 := h2 ▸ h1
  sorry
