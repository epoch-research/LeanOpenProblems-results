import Submission.FilteredExposureBarrier
import Submission.PhaseUnionBennett

/-! Soft exposure with exceptional partial-population floors. The exceptional
probability is charged explicitly; no small bound for it is asserted. -/
namespace Erdos970.SoftExposure
open Finset Real GapAverages
set_option maxHeartbeats 1000000

noncomputable def exceptionalPartialFraction (P : Finset ℕ) (m j : ℕ) (A : ℝ) : ℝ := by
  classical
  exact phaseMean P (fun r =>
    if PartialLower j (range m) P (phaseResidues P r) A then 0 else 1)

lemma exceptionalPartialFraction_nonneg (P : Finset ℕ) (m j : ℕ) (A : ℝ) :
    0 ≤ exceptionalPartialFraction P m j A := by
  classical
  unfold exceptionalPartialFraction phaseMean
  positivity

/-- Bad partial floors are retained as a probability, rather than implicitly
excluded by a residue-uniform hypothesis. -/
theorem lowCountFraction_mul_le_budget_add_exceptional
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (m j : ℕ)
    (A b : ℝ) (hA : 0 < A) (hb : 0 ≤ b) (hbA : b ≤ A) :
    (1-b/A)^j * lowCountFraction P m b ≤ budget j P +
      (1-b/A)^j * exceptionalPartialFraction P m j A := by
  classical
  have hpow : 0 ≤ (1-b/A)^j :=
    pow_nonneg (sub_nonneg.mpr ((div_le_one hA).mpr hbA)) j
  have hpoint (r : Phase P) :
      (1-b/A)^j * (if intervalCount P m r ≤ b then 1 else 0) ≤
        tree j (range m) P (phaseResidues P r) + (1-b/A)^j *
          (if PartialLower j (range m) P (phaseResidues P r) A then 0 else 1) := by
    by_cases hf : PartialLower j (range m) P (phaseResidues P r) A
    · rw [if_pos hf, mul_zero, add_zero]
      split_ifs with hr
      · rw [mul_one]
        apply tree_lower j (range m) P (phaseResidues P r) A b hA hb hbA hf
        rw [survivors_phase, Resampling.populationSurvivors_card]
        exact hr
      · simpa only [mul_zero] using tree_nonneg j (range m) P (phaseResidues P r)
    · rw [if_neg hf, mul_one]
      have ht := tree_nonneg j (range m) P (phaseResidues P r)
      split_ifs <;> simp only [mul_one, mul_zero] <;> linarith
  have hh := phaseMean_mono P hpoint
  rw [phaseMean_add, phaseMean_mul, phaseMean_mul] at hh
  exact hh.trans (add_le_add (tree_mean_le_budget j (range m) P hP) le_rfl)

/-- An unconditional lower-tail estimate with its exceptional term visible.
The strict inequality b<A is needed only for division. -/
theorem lowCountFraction_le_budget_div_add_exceptional
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (m j : ℕ)
    (A b : ℝ) (hA : 0 < A) (hb : 0 ≤ b) (hbA : b < A) :
    lowCountFraction P m b ≤ budget j P/(1-b/A)^j +
      exceptionalPartialFraction P m j A := by
  have hh := lowCountFraction_mul_le_budget_add_exceptional P hP m j A b hA hb hbA.le
  have hpow : 0 < (1-b/A)^j :=
    pow_pos (sub_pos.mpr ((div_lt_one hA).mpr hbA)) j
  have hd : lowCountFraction P m b ≤
      (budget j P + (1-b/A)^j * exceptionalPartialFraction P m j A)/(1-b/A)^j := by
    apply (le_div_iff₀ hpow).mpr
    simpa only [mul_comm] using hh
  simpa only [add_div, mul_div_cancel_left₀ _ hpow.ne'] using hd

/-- Taking a marginal on retained coordinates preserves the independent
uniform phase average. This applies to arbitrary real-valued statistics. -/
lemma phaseMean_corePhase (P Q : Finset ℕ) (hQP : Q ⊆ P)
    (hP : ∀ p ∈ P, p.Prime) (F : Phase Q → ℝ) :
    phaseMean P (fun r => F (corePhase P Q hQP r)) = phaseMean Q F := by
  let R := P \ Q
  have hdis : Disjoint Q R := by
    apply disjoint_left.mpr
    intro p hp hpr
    exact (mem_sdiff.mp hpr).2 hp
  have hU : Q ∪ R = P := union_sdiff_of_subset hQP
  have hR : ∀ p ∈ R, p.Prime := fun p hp => hP p (mem_sdiff.mp hp).1
  suffices hf : ∀ (T : Finset ℕ) (hQT : Q ⊆ T), Q ∪ R = T →
      phaseMean T (fun r => F (corePhase T Q hQT r)) = phaseMean Q F by
    exact hf P hQP hU
  intro T hQT heq
  subst T
  rw [phaseMean_union Q R hdis]
  have he (r : Phase Q) (s : Phase R) :
      corePhase (Q ∪ R) Q hQT (joinPhase Q R r s) = r := by
    funext q
    exact joinPhase_left Q R r s q
  simp_rw [he, phaseMean_const R hR]

noncomputable def strictLowCountFraction (P : Finset ℕ) (m : ℕ) (A : ℝ) : ℝ :=
  phaseMean P (fun r => if intervalCount P m r < A then 1 else 0)

lemma strictLowCountFraction_le (P : Finset ℕ) (m : ℕ) (A : ℝ) :
    strictLowCountFraction P m A ≤ lowCountFraction P m A := by
  apply phaseMean_mono P
  intro r
  split_ifs <;> simp_all <;> linarith

/-- The union bound is over all smaller subcores, not merely prefixes of
one chosen ordering. These probabilities share coordinates; independence
between the exceptional events is not asserted. -/
theorem exceptionalPartialFraction_le_subcore_sum
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (m j : ℕ) (A : ℝ) :
    exceptionalPartialFraction P m j A ≤
      ∑ Q ∈ P.powerset.filter (fun Q => Q.card < j), strictLowCountFraction Q m A := by
  classical
  let S := P.powerset.filter (fun Q => Q.card < j)
  have hpoint (r : Phase P) :
      (if PartialLower j (range m) P (phaseResidues P r) A then (0 : ℝ) else 1) ≤
        ∑ Q ∈ S, if ((survivors (range m) Q (phaseResidues P r)).card : ℝ) < A
          then 1 else 0 := by
    split_ifs with hf
    · exact sum_nonneg (fun Q _ => by split_ifs <;> norm_num)
    · have he : ∃ Q, Q ⊆ P ∧ Q.card < j ∧
          ((survivors (range m) Q (phaseResidues P r)).card : ℝ) < A := by
        simpa only [PartialLower, not_forall, Classical.not_imp, not_le, exists_prop] using hf
      obtain ⟨Q,hQP,hQj,hQ⟩ := he
      have hQS : Q ∈ S := mem_filter.mpr ⟨mem_powerset.mpr hQP,hQj⟩
      have hh := single_le_sum (s := S)
        (f := fun T => if ((survivors (range m) T (phaseResidues P r)).card : ℝ) < A
          then (1 : ℝ) else 0)
        (fun T _ => by dsimp only; split_ifs <;> norm_num) hQS
      simpa only [hQ,if_true] using hh
  have hh := phaseMean_mono P hpoint
  rw [phaseMean_sum] at hh
  apply hh.trans_eq
  apply sum_congr rfl
  intro Q hQS
  have hQP : Q ⊆ P := mem_powerset.mp (mem_filter.mp hQS).1
  have he (r : Phase P) :
      ((survivors (range m) Q (phaseResidues P r)).card : ℝ) =
        intervalCount Q m (corePhase P Q hQP r) := by
    rw [partial_survivors_eq_core P Q hQP m r, CoverFibers.phaseSurvivors_card]
  simp_rw [he]
  exact phaseMean_corePhase P Q hQP hP (fun r => if intervalCount Q m r < A then 1 else 0)

/-- An explicit recursive bound in which every exceptional subcore is
charged. If j≤P.card, all subcores on the right have smaller cardinality. -/
theorem lowCountFraction_le_budget_div_add_subcore_sum
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (m j : ℕ)
    (A b : ℝ) (hA : 0 < A) (hb : 0 ≤ b) (hbA : b < A) :
    lowCountFraction P m b ≤ budget j P/(1-b/A)^j +
      ∑ Q ∈ P.powerset.filter (fun Q => Q.card < j), strictLowCountFraction Q m A :=
  (lowCountFraction_le_budget_div_add_exceptional P hP m j A b hA hb hbA).trans
    (add_le_add le_rfl (exceptionalPartialFraction_le_subcore_sum P hP m j A))

#print axioms lowCountFraction_le_budget_div_add_exceptional
#print axioms lowCountFraction_mul_le_budget_add_exceptional
#print axioms strictLowCountFraction_le
#print axioms lowCountFraction_le_budget_div_add_subcore_sum
#print axioms phaseMean_corePhase
#print axioms exceptionalPartialFraction_le_subcore_sum
end Erdos970.SoftExposure
