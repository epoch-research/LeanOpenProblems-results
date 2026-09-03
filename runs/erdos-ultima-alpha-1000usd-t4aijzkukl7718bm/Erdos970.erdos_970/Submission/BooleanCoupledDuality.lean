import Submission.BooleanKernelDuality
import Submission.FirstHitDisjointCost

/-! Restricted-moment dual certificates for first-hit objectives, and a general
coverage-polynomial criterion not requiring nonnegative first-hit increments. -/
namespace Erdos970.FiniteSelberg
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma weighted_boolean_error_supported (q : ι → ℝ) (X : ℝ)
    (w : (ι → Bool) → ℝ) (a : Finset ι → ℝ)
    (hw : ∀ T : Finset ι, a T ≠ 0 →
      |(∑ ω, w ω * hitMonomial T ω) - X * ∏ i ∈ T, q i| ≤ 1) :
    |(∑ ω, w ω * booleanValue a ω) -
      X * (∑ T : Finset ι, a T * ∏ i ∈ T, q i)| ≤ ∑ T : Finset ι, |a T| := by
  have heq : (∑ ω, w ω * booleanValue a ω) -
      X * (∑ T : Finset ι, a T * ∏ i ∈ T, q i) =
      ∑ T : Finset ι, a T * ((∑ ω, w ω * hitMonomial T ω) - X * ∏ i ∈ T, q i) := by
    simp only [booleanValue, mul_sum, mul_sub, sum_sub_distrib]
    rw [sum_comm]
    congr 1
    · apply sum_congr rfl
      intro T hT
      apply sum_congr rfl
      intro ω hω
      ring
    · apply sum_congr rfl
      intro T hT
      ring
  rw [heq]
  apply (abs_sum_le_sum_abs _ _).trans
  apply sum_le_sum
  intro T hT
  by_cases ha : a T = 0
  · simp [ha]
  · rw [abs_mul]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (hw T ha) (abs_nonneg (a T))

lemma booleanObjective_supported_dual_bound (q : ι → ℝ) (X : ℝ)
    (w : (ι → Bool) → ℝ) (hw0 : ∀ ω, 0 ≤ w ω)
    (a : Finset ι → ℝ) (ha : ∀ ω, 0 ≤ booleanValue a ω)
    (hnorm : booleanValue a (fun _ => false) = 1)
    (hw : ∀ T : Finset ι, a T ≠ 0 →
      |(∑ ω, w ω * hitMonomial T ω) - X * ∏ i ∈ T, q i| ≤ 1) :
    w (fun _ => false) ≤ booleanObjective q X a := by
  have hlower := single_le_sum (s := univ) (f := fun ω => w ω * booleanValue a ω)
    (fun ω _ => mul_nonneg (hw0 ω) (ha ω)) (mem_univ (fun _ => false))
  change w (fun _ => false) * booleanValue a (fun _ => false) ≤
    ∑ ω, w ω * booleanValue a ω at hlower
  rw [hnorm, mul_one] at hlower
  have he := (abs_le.mp (weighted_boolean_error_supported q X w a hw)).2
  unfold booleanObjective
  linarith

section Ordered
variable [LinearOrder ι]

/-- Only prior-coordinate moments need be checked for each first-hit dual. -/
def FirstHitDualFeasible (q : ι → ℝ) (m : ℝ) (w : ι → (ι → Bool) → ℝ) : Prop :=
  (∀ i ω, 0 ≤ w i ω) ∧ ∀ i T, (∀ j ∈ T, j < i) →
    |(∑ ω, w i ω * hitMonomial T ω) - (m * q i) * ∏ j ∈ T, q j| ≤ 1

/-- A joint lower bound on every signed normalized prior-supported first-hit
family, with exact Boolean coefficient costs. -/
theorem firstHit_objective_dual_bound (q : ι → ℝ) (m : ℝ)
    (w : ι → (ι → Bool) → ℝ) (hw : FirstHitDualFeasible q m w)
    (c : ι → Finset ι → ℝ)
    (hc : ∀ i, (∑ Q : Finset ι, c i Q) = 1)
    (hprior : ∀ i Q, c i Q ≠ 0 → ∀ j ∈ Q, j < i) :
    (∑ i, w i (fun _ => false)) ≤ ∑ i, booleanKernelObjective q (m * q i) (c i) := by
  apply sum_le_sum
  intro i hi
  rw [← booleanObjective_square]
  apply booleanObjective_supported_dual_bound q (m * q i) (w i) (hw.1 i)
  · intro ω
    rw [booleanValue_square]
    exact sq_nonneg _
  · rw [booleanValue_square]
    simp [linearKernel, basis_at_empty, hc i]
  · intro T hT
    apply hw.2 i T
    exact booleanSquareCoefficient_prior _ i (ordinaryCoefficient_prior q c hprior i) T hT

end Ordered

/-- A normalized coverage majorant has value at least one at every nonempty
pattern and zero constant coefficient. Its increments need not be nonnegative. -/
def IsCoverageMajorant (a : Finset ι → ℝ) : Prop :=
  a ∅ = 0 ∧ ∀ ω : ι → Bool, ω ≠ (fun _ => false) → 1 ≤ booleanValue a ω

/-- A global coverage polynomial guarantees a survivor when its objective is <m. -/
theorem survivor_of_coverage_majorant (q : ι → ℝ) (m : ℕ)
    (a : Finset ι → ℝ) (ha : IsCoverageMajorant a)
    (ω : ℕ → ι → Bool)
    (herr : ∀ T : Finset ι,
      |(∑ j ∈ range m, hitMonomial T (ω j)) - (m : ℝ) * ∏ i ∈ T, q i| ≤ 1)
    (hobj : booleanObjective q m a < m) :
    ∃ j < m, ∀ i, ω j i = false := by
  by_contra hbad
  push_neg at hbad
  have hlower : (m : ℝ) ≤ ∑ j ∈ range m, booleanValue a (ω j) := by
    calc
      _ = ∑ j ∈ range m, (1 : ℝ) := by simp
      _ ≤ _ := by
        apply sum_le_sum
        intro j hj
        apply ha.2 (ω j)
        intro he
        obtain ⟨i, hi⟩ := hbad j (mem_range.mp hj)
        exact hi (congrFun he i)
  have he := finite_polynomial_interval_error univ a id q m ω herr
  change |(∑ j ∈ range m, booleanValue a (ω j)) -
    (m : ℝ) * average q (booleanValue a)| ≤ ∑ T : Finset ι, |a T| at he
  have havg : average q (booleanValue a) = ∑ T : Finset ι, a T * ∏ i ∈ T, q i := by
    unfold booleanValue
    rw [average_sum]
    simp only [average_mul_const, average_hitMonomial]
  rw [havg] at he
  unfold booleanObjective at hobj
  linarith [(abs_le.mp he).2]

/-- Dual optimality for global coverage polynomials. The population has no empty
atom, and only nonempty intersection moments are constrained. -/
theorem coverageObjective_dual_bound (q : ι → ℝ) (m : ℝ)
    (w : (ι → Bool) → ℝ) (hw0 : ∀ ω, 0 ≤ w ω) (hwempty : w (fun _ => false) = 0)
    (hw : ∀ T : Finset ι, T.Nonempty →
      |(∑ ω, w ω * hitMonomial T ω) - m * ∏ i ∈ T, q i| ≤ 1)
    (a : Finset ι → ℝ) (ha : IsCoverageMajorant a) :
    (∑ ω, w ω) ≤ booleanObjective q m a := by
  have hlower : (∑ ω, w ω) ≤ ∑ ω, w ω * booleanValue a ω := by
    apply sum_le_sum
    intro ω hω
    by_cases he : ω = (fun _ => false)
    · simp [he, hwempty]
    · simpa only [mul_one] using mul_le_mul_of_nonneg_left (ha.2 ω he) (hw0 ω)
  have he := weighted_boolean_error_supported q m w a (fun T hT => hw T (by
    by_contra hn
    have hz : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    exact hT (hz ▸ ha.1)))
  unfold booleanObjective
  linarith [(abs_le.mp he).2]

#print axioms firstHit_objective_dual_bound
#print axioms survivor_of_coverage_majorant
#print axioms coverageObjective_dual_bound
end Erdos970.FiniteSelberg
