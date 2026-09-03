import Submission.ResampledExactBudgetBarrier

/-! Averaging the uniform deterministic partial-count hypothesis supplies
precisely the floors used in the exact resampling-budget comparison. -/
namespace Erdos970.SoftExposure
open Finset Real GapAverages Resampling
set_option maxHeartbeats 0

lemma uniform_partial_count_of_phase (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (m j : ℕ) (A : ℝ)
    (hpartial : ∀ r : Phase P, PartialLower j (range m) P (phaseResidues P r) A)
    (U : Finset ℕ) (hUP : U ⊆ P) (hUj : U.card < j) (u : Phase U) :
    A ≤ intervalCount U m u := by
  classical
  let s : Phase P := fun p => if hp : p.val ∈ U then u ⟨p.val,hp⟩
    else ⟨0,(hP p.val p.property).pos⟩
  have he : corePhase P U hUP s = u := by
    funext p
    simp only [corePhase,s,p.property,dif_pos]
  have hh := partial_lower_core_count P U hUP m j A s (hpartial s) hUj
  rwa [he] at hh

lemma phaseMean_join_count (Q T : Finset ℕ) (hdis : Disjoint Q T)
    (hT : ∀ p ∈ T, p.Prime) (m : ℕ) (r : Phase Q) :
    phaseMean T (fun s => intervalCount (Q ∪ T) m (joinPhase Q T r s)) =
      intervalCount Q m r * density T := by
  have he (s : Phase T) : intervalCount (Q ∪ T) m (joinPhase Q T r s) =
      ((populationSurvivors (populationSurvivors (range m) Q r) T s).card : ℝ) := by
    rw [← populationSurvivors_union _ _ _ hdis, populationSurvivors_card]
    rfl
  simp_rw [he]
  rw [populationSurvivors_mean _ T hT, populationSurvivors_card]
  rfl

/-- Averaging extra partial coordinates gives a deterministic lower bound
on every fixed core count, without assuming a covered full phase. -/
theorem averaged_partial_floor (P Q : Finset ℕ) (hQP : Q ⊆ P)
    (hP : ∀ p ∈ P, p.Prime) (m j : ℕ) (A : ℝ)
    (hpartial : ∀ r : Phase P, PartialLower j (range m) P (phaseResidues P r) A)
    (r : Phase Q) (T : Finset ℕ) (hTP : T ⊆ P \ Q) (hTj : T.card < j-Q.card) :
    A ≤ intervalCount Q m r * density T := by
  have hT : ∀ p ∈ T, p.Prime := fun p hp => hP p (mem_sdiff.mp (hTP hp)).1
  have hdis : Disjoint Q T := disjoint_left.mpr
    (fun p hpQ hpT => (mem_sdiff.mp (hTP hpT)).2 hpQ)
  have hUP : Q ∪ T ⊆ P := union_subset hQP (fun p hp => (mem_sdiff.mp (hTP hp)).1)
  have hUj : (Q ∪ T).card < j := by
    rw [card_union_of_disjoint hdis]
    omega
  have hh := phaseMean_mono T (fun s =>
    uniform_partial_count_of_phase P hP m j A hpartial (Q ∪ T) hUP hUj
      (joinPhase Q T r s))
  rwa [phaseMean_const T hT A,phaseMean_join_count Q T hdis hT m r] at hh

/-- Any valid upper bound D on a core count must satisfy all of the
averaged partial floors. This uses no probabilistic lower-tail estimate. -/
theorem averaged_partial_floor_of_count_le (P Q : Finset ℕ) (hQP : Q ⊆ P)
    (hP : ∀ p ∈ P, p.Prime) (m j : ℕ) (A D : ℝ)
    (hpartial : ∀ r : Phase P, PartialLower j (range m) P (phaseResidues P r) A)
    (r : Phase Q) (hD : intervalCount Q m r ≤ D)
    (T : Finset ℕ) (hTP : T ⊆ P \ Q) (hTj : T.card < j-Q.card) :
    A ≤ D*density T := by
  exact (averaged_partial_floor P Q hQP hP m j A hpartial r T hTP hTj).trans
    (mul_le_mul_of_nonneg_right hD (density_pos T
      (fun p hp => hP p (mem_sdiff.mp (hTP hp)).1)).le)

/-- A strict resampling/exposure comparison must already violate some
averaged deterministic partial floor. The exact factorial budget, rather
than a reciprocal-sum majorant, is used in this result. -/
theorem strict_markov_budget_requires_violated_floor (P Q : Finset ℕ)
    (hQP : Q ⊆ P) (hP : ∀ p ∈ P, p.Prime) (j : ℕ)
    (A b D : ℝ) (hA : 0 < A) (hb : 0 < b) (hbA : b ≤ A) (hD : 0 ≤ D)
    (hstrict : budget j P <
      (1-b/A)^j * ((1-D*density (P \ Q)/b)*(∏ q ∈ Q, (q : ℝ)⁻¹))) :
    ∃ T ⊆ P \ Q, T.card < j-Q.card ∧ D*density T < A := by
  classical
  have hQj : Q.card ≤ j := by
    by_contra hh
    exact hstrict.not_ge (markov_expression_le_budget_of_large_core P Q hQP hP j
      (by omega) A b D hA hb hbA hD)
  by_contra hh
  push_neg at hh
  have hf : ∀ T ⊆ P \ Q, T.card < j-Q.card → A ≤ D*density T := by
    intro T hT hc
    exact hh T hT hc
  exact hstrict.not_ge (markov_expression_le_exact_budget P Q hQP hP j hQj
    A b D hA hb hbA hD hf)

/-- The same core-count contradiction can be obtained directly by averaging,
without invoking the full-phase soft-exposure probability bound. -/
theorem no_small_core_count_of_strict_markov_budget (P Q : Finset ℕ)
    (hQP : Q ⊆ P) (hP : ∀ p ∈ P, p.Prime) (m j : ℕ)
    (A b D : ℝ) (hA : 0 < A) (hb : 0 < b) (hbA : b ≤ A) (hD : 0 ≤ D)
    (hpartial : ∀ r : Phase P, PartialLower j (range m) P (phaseResidues P r) A)
    (hstrict : budget j P <
      (1-b/A)^j * ((1-D*density (P \ Q)/b)*(∏ q ∈ Q, (q : ℝ)⁻¹)))
    (r : Phase Q) : D < intervalCount Q m r := by
  obtain ⟨T,hT,hTj,hbad⟩ := strict_markov_budget_requires_violated_floor P Q hQP hP j
    A b D hA hb hbA hD hstrict
  by_contra hh
  exact hbad.not_ge (averaged_partial_floor_of_count_le P Q hQP hP m j A D
    hpartial r (le_of_not_gt hh) T hT hTj)

#print axioms averaged_partial_floor
#print axioms averaged_partial_floor_of_count_le
#print axioms strict_markov_budget_requires_violated_floor
#print axioms no_small_core_count_of_strict_markov_budget
end Erdos970.SoftExposure
