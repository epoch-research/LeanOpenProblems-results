import FormalConjectures.Util.ProblemImports
open Nat Finset

lemma sum_padic_le (p : ℕ) [Fact p.Prime] (A B : ℕ) :
  padicValNat p (∏ x ∈ Icc A B, x) = ∑ x ∈ Icc A B, padicValNat p x := by
  sorry
