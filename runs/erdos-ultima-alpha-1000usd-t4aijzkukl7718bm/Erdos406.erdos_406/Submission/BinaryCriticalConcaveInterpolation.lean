import Submission.BinaryCriticalMinObserver

/-! Exact finite interpolation by supporting linear forms. This describes
finite samples only: it does not assert any unsampled construction inequality. -/
namespace Erdos406BinaryCriticalMinObserver
open scoped Matrix BigOperators
variable {ι τ σ : Type*} [Fintype ι] [Nonempty ι] [Fintype σ]

lemma minValue_eq_support (x u : ι → σ → ℝ)
    (hsupport : ∀ i j, u j ⬝ᵥ x j≤u i ⬝ᵥ x j) (j : ι) :
    minValue (fun i => u i ⬝ᵥ x j)=u j ⬝ᵥ x j := by
  apply le_antisymm
  · exact minValue_le _ j
  · exact le_minValue _ _ (fun i => hsupport i j)

/-- Any finite minimum of linear forms has such a supporting-plane
representation at the sampled points, even when its original number of
pieces differs from the number of samples. -/
theorem finite_min_supports [Fintype τ] [Nonempty τ]
    (x : ι → σ → ℝ) (U : τ → σ → ℝ) :
    ∃ u : ι → σ → ℝ,
      (∀ i, ∃ t, u i=U t) ∧
      (∀ i j, u j ⬝ᵥ x j≤u i ⬝ᵥ x j) ∧
      (∀ j, minValue (fun i => u i ⬝ᵥ x j)=minValue (fun t => U t ⬝ᵥ x j)) := by
  classical
  have hh : ∀ j : ι, ∃ t : τ, minValue (fun t => U t ⬝ᵥ x j)=U t ⬝ᵥ x j :=
    fun j => minValue_attained _
  choose f hf using hh
  let u : ι → σ → ℝ := fun j => U (f j)
  have hs : ∀ i j, u j ⬝ᵥ x j≤u i ⬝ᵥ x j := by
    intro i j
    change U (f j) ⬝ᵥ x j≤U (f i) ⬝ᵥ x j
    rw [← hf j]
    exact minValue_le _ (f i)
  refine ⟨u,fun i => ⟨f i,rfl⟩,hs,?_⟩
  intro j
  rw [minValue_eq_support x u hs j]
  exact (hf j).symm

/-- Assigned sample values admit a finite minimum representation if and only
if there are supporting forms with linear anchor and cross inequalities. -/
theorem finite_min_interpolation_iff (x : ι → σ → ℝ) (y : ι → ℝ) :
    (∃ U : ι → σ → ℝ, ∀ j, minValue (fun i => U i ⬝ᵥ x j)=y j) ↔
    ∃ u : ι → σ → ℝ, (∀ j, u j ⬝ᵥ x j=y j) ∧ (∀ i j, y j≤u i ⬝ᵥ x j) := by
  constructor
  · rintro ⟨U,hU⟩
    obtain ⟨u,_,hs,hy⟩ := finite_min_supports x U
    have he (j : ι) : u j ⬝ᵥ x j=y j := by
      rw [← minValue_eq_support x u hs j,hy j,hU j]
    exact ⟨u,he,fun i j => (he j) ▸ hs i j⟩
  · rintro ⟨u,hu,hcross⟩
    refine ⟨u,?_⟩
    intro j
    apply le_antisymm
    · exact (minValue_le _ j).trans (hu j).le
    · exact le_minValue _ _ (fun i => hcross i j)

#print axioms minValue_eq_support
#print axioms finite_min_supports
#print axioms finite_min_interpolation_iff
end Erdos406BinaryCriticalMinObserver
