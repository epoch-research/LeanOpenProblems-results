import FormalConjectures.Util.ProblemImports

open Nat Finset

lemma padicValNat_prod {α : Type} (p : ℕ) [Fact p.Prime] (s : Finset α) (f : α → ℕ)
  (h : ∀ x ∈ s, f x ≠ 0) :
  padicValNat p (∏ x ∈ s, f x) = ∑ x ∈ s, padicValNat p (f x) := by
  sorry
