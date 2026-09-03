import Submission.ConicExceptionalParameters

/-! A positive-density source with a reciprocal-summable set of surviving
primitive parameters for the explicit conic. -/
namespace Erdos1206.SummableConicSource
open GeometricConicSource ConicExceptionalParameters SquarefreeConicFamily
open scoped Classical

noncomputable def survivors (A : Set ℕ) : Set (ℕ × ℕ) :=
  {v | Nat.Coprime v.1 v.2 ∧ 0 < v.2 ∧ ∃ x : Fin 4 → ℕ, 0 < x 0 ∧
    (∀ i, x i*F 0 v.1 v.2=x 0*F i v.1 v.2) ∧ ∀ i, x i ∈ A}

theorem exists_source_summable_parameters :
    ∃ A : Set ℕ, (∀ n ∈ A, Squarefree n) ∧ 0 < A.lowerDensity ∧
      Summable (DyadicBoxReciprocal.weight (survivors A)) := by
  obtain ⟨A,k,hAS,hAd,hk,hbound⟩ := exists_source_threshold
  have hs := exceptional_reciprocal_summable k hk
  refine ⟨A,hAS,hAd,hs.of_nonneg_of_le (DyadicBoxReciprocal.weight_nonneg _) ?_⟩
  intro v
  by_cases hv : v ∈ survivors A
  · have hvmem := hv
    obtain ⟨hcop,hu,x,hx,hprop,hmem⟩ := hv
    have he : v ∈ exceptional k := ⟨hu,fun j => hbound j v.1 v.2 x hcop hu hx hprop hmem⟩
    simp only [DyadicBoxReciprocal.weight,if_pos hvmem,if_pos he,le_refl]
  · rw [DyadicBoxReciprocal.weight,if_neg hv]
    exact DyadicBoxReciprocal.weight_nonneg _ _

#print axioms exists_source_summable_parameters
end Erdos1206.SummableConicSource
