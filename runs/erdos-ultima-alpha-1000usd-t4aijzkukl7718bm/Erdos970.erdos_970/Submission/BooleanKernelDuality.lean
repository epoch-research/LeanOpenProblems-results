import Submission.FirstHitBooleanCost

/-! Nonnegative finite-population certificates give global lower bounds for the
Boolean-reduced upper-kernel objective. This is weak duality, not an assertion
that a suitable uniform Jacobsthal bound or a particular dual population exists. -/
namespace Erdos970.FiniteSelberg
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def booleanValue (a : Finset ι → ℝ) (ω : ι → Bool) : ℝ :=
  ∑ T : Finset ι, a T * hitMonomial T ω

noncomputable def booleanObjective (q : ι → ℝ) (X : ℝ) (a : Finset ι → ℝ) : ℝ :=
  X * (∑ T : Finset ι, a T * ∏ i ∈ T, q i) + ∑ T : Finset ι, |a T|

/-- A nonnegative population whose intersection moments have errors at most one. -/
def BooleanDualFeasible (q : ι → ℝ) (X : ℝ) (w : (ι → Bool) → ℝ) : Prop :=
  (∀ ω, 0 ≤ w ω) ∧ ∀ T : Finset ι,
    |(∑ ω, w ω * hitMonomial T ω) - X * ∏ i ∈ T, q i| ≤ 1

lemma weighted_boolean_error (q : ι → ℝ) (X : ℝ) (w : (ι → Bool) → ℝ)
    (hw : ∀ T : Finset ι,
      |(∑ ω, w ω * hitMonomial T ω) - X * ∏ i ∈ T, q i| ≤ 1)
    (a : Finset ι → ℝ) :
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
  rw [abs_mul]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left (hw T) (abs_nonneg (a T))

/-- Weak duality for every normalized nonnegative Boolean upper weight. -/
theorem booleanObjective_dual_bound (q : ι → ℝ) (X : ℝ)
    (w : (ι → Bool) → ℝ) (hw : BooleanDualFeasible q X w)
    (a : Finset ι → ℝ) (ha : ∀ ω, 0 ≤ booleanValue a ω)
    (hnorm : booleanValue a (fun _ => false) = 1) :
    w (fun _ => false) ≤ booleanObjective q X a := by
  have hlower := single_le_sum (s := univ) (f := fun ω => w ω * booleanValue a ω)
    (fun ω _ => mul_nonneg (hw.1 ω) (ha ω)) (mem_univ (fun _ => false))
  change w (fun _ => false) * booleanValue a (fun _ => false) ≤
    ∑ ω, w ω * booleanValue a ω at hlower
  rw [hnorm, mul_one] at hlower
  have he := (abs_le.mp (weighted_boolean_error q X w hw.2 a)).2
  unfold booleanObjective
  linarith

/-- Matching a feasible dual population certifies global optimality, without
trusting an optimizer or assuming coefficient signs. -/
theorem booleanObjective_minimizes (q : ι → ℝ) (X : ℝ)
    (w : (ι → Bool) → ℝ) (hw : BooleanDualFeasible q X w)
    (b : Finset ι → ℝ) (hb : booleanObjective q X b = w (fun _ => false))
    (a : Finset ι → ℝ) (ha : ∀ ω, 0 ≤ booleanValue a ω)
    (hnorm : booleanValue a (fun _ => false) = 1) :
    booleanObjective q X b ≤ booleanObjective q X a := by
  rw [hb]
  exact booleanObjective_dual_bound q X w hw a ha hnorm

noncomputable def booleanKernelObjective (q : ι → ℝ) (X : ℝ)
    (c : Finset ι → ℝ) : ℝ :=
  X * average q (fun ω => linearKernel q c ω ^ 2) +
    booleanSquareCost (ordinaryCoefficient q c)

lemma booleanValue_square (q : ι → ℝ) (c : Finset ι → ℝ) (ω : ι → Bool) :
    booleanValue (booleanSquareCoefficient (ordinaryCoefficient q c)) ω =
      linearKernel q c ω ^ 2 := by
  rw [linearKernel_expansion, booleanSquare_expansion]
  rfl

lemma booleanObjective_square (q : ι → ℝ) (X : ℝ) (c : Finset ι → ℝ) :
    booleanObjective q X (booleanSquareCoefficient (ordinaryCoefficient q c)) =
      booleanKernelObjective q X c := by
  have havg : average q (fun ω => linearKernel q c ω ^ 2) =
      ∑ T : Finset ι, booleanSquareCoefficient (ordinaryCoefficient q c) T * ∏ i ∈ T, q i := by
    simp_rw [← booleanValue_square, booleanValue]
    rw [average_sum]
    simp only [average_mul_const, average_hitMonomial]
  simp only [booleanObjective, booleanKernelObjective, havg, booleanSquareCost]

/-- The same certificate bounds ALL signed orthogonal kernels of sum one. -/
theorem booleanKernelObjective_dual_bound (q : ι → ℝ) (X : ℝ)
    (w : (ι → Bool) → ℝ) (hw : BooleanDualFeasible q X w)
    (c : Finset ι → ℝ) (hc : (∑ Q : Finset ι, c Q) = 1) :
    w (fun _ => false) ≤ booleanKernelObjective q X c := by
  rw [← booleanObjective_square]
  apply booleanObjective_dual_bound q X w hw
  · intro ω
    rw [booleanValue_square]
    exact sq_nonneg _
  · rw [booleanValue_square]
    simp [linearKernel, basis_at_empty, hc]

#print axioms booleanObjective_minimizes
#print axioms booleanKernelObjective_dual_bound
end Erdos970.FiniteSelberg
