import FormalConjectures.Util.ProblemImports
open Nat Finset

def A335226_condition (m : ℕ) : Prop :=
  let goldbach_count (N : ℕ) : ℕ :=
    (Finset.range (N / 2 + 1)).filter (fun p => p.Prime ∧ (N - p).Prime) |>.card
  2 * goldbach_count (2 * m) < goldbach_count (4 * m)

noncomputable def A335226 (n : ℕ) : ℕ := n.nth A335226_condition

theorem A335226_conjecture :
  A335226 114 = 22564 ∧ (∀ m : ℕ, m > 22564 → ¬ A335226_condition m) := by
  sorry

theorem A335226_conjecture.disproof : ¬ (type_of% @A335226_conjecture) := by
  sorry
