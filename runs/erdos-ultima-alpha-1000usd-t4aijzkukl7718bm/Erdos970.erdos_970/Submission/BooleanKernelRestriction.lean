import Submission.BooleanKernelTailReduction

/-! An explicit coefficient operator implementing the rare-coordinate reduction
inside the signed-kernel class, with normalization and prior support preserved. -/
namespace Erdos970.FiniteSelberg
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def restrictOrthogonal (S : Finset ι) (c : Finset ι → ℝ)
    (R : Finset ι) : ℝ := ∑ Q : Finset ι, if Q ∩ S = R then c Q else 0

lemma basis_restrictPattern (q : ι → ℝ) (S Q : Finset ι) (ω : ι → Bool) :
    basis q Q (restrictBooleanPattern S ω) = basis q (Q ∩ S) ω := by
  unfold basis
  apply prod_congr rfl
  intro i hi
  by_cases hiQ : i ∈ Q <;> by_cases hiS : i ∈ S <;>
    simp [restrictBooleanPattern, hiQ, hiS, contrast]

lemma restrictOrthogonal_sum (S : Finset ι) (c : Finset ι → ℝ) :
    (∑ R : Finset ι, restrictOrthogonal S c R) = ∑ Q : Finset ι, c Q := by
  unfold restrictOrthogonal
  rw [sum_comm]
  simp

lemma linearKernel_restrictOrthogonal (q : ι → ℝ) (S : Finset ι)
    (c : Finset ι → ℝ) (ω : ι → Bool) :
    linearKernel q (restrictOrthogonal S c) ω =
      linearKernel q c (restrictBooleanPattern S ω) := by
  simp only [linearKernel, restrictOrthogonal, sum_mul, ite_mul, zero_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro Q hQ
  rw [basis_restrictPattern]
  simp

lemma restrictOrthogonal_nonzero (S : Finset ι) (c : Finset ι → ℝ) (R : Finset ι)
    (hR : restrictOrthogonal S c R ≠ 0) :
    ∃ Q : Finset ι, c Q ≠ 0 ∧ Q ∩ S = R := by
  obtain ⟨Q, _, hQ⟩ := exists_ne_zero_of_sum_ne_zero hR
  by_cases he : Q ∩ S = R
  · exact ⟨Q, by simpa [he] using hQ, he⟩
  · simp [he] at hQ

lemma restrictOrthogonal_supported (S : Finset ι) (c : Finset ι → ℝ) (R : Finset ι)
    (hR : restrictOrthogonal S c R ≠ 0) : R ⊆ S := by
  obtain ⟨Q, _, hQ⟩ := restrictOrthogonal_nonzero S c R hR
  rw [← hQ]
  exact inter_subset_right

/-- Restricting the kernel really restricts its squared coefficient list exactly. -/
lemma booleanSquare_restrictOrthogonal (q : ι → ℝ) (S : Finset ι)
    (c : Finset ι → ℝ) :
    booleanSquareCoefficient (ordinaryCoefficient q (restrictOrthogonal S c)) =
      restrictBooleanCoefficient S (booleanSquareCoefficient (ordinaryCoefficient q c)) := by
  apply booleanValue_injective
  funext ω
  rw [booleanValue_square, booleanValue_restrict, booleanValue_square,
    linearKernel_restrictOrthogonal]

/-- This explicit operator never increases the exact Boolean-cost objective
when every discarded coordinate has expected hit mass at most one. -/
theorem booleanKernelObjective_restrict_le (q : ι → ℝ) (X : ℝ)
    (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1) (hX : 0 ≤ X)
    (S : Finset ι) (hsmall : ∀ i ∉ S, X * q i ≤ 1) (c : Finset ι → ℝ) :
    booleanKernelObjective q X (restrictOrthogonal S c) ≤ booleanKernelObjective q X c := by
  rw [← booleanObjective_square, ← booleanObjective_square, booleanSquare_restrictOrthogonal]
  exact booleanObjective_restrict_le q X hq hX S hsmall _

section Ordered
variable [LinearOrder ι]

noncomputable def reduceFirstHitKernels (q : ι → ℝ) (m : ℝ)
    (c : ι → Finset ι → ℝ) (i : ι) : Finset ι → ℝ :=
  restrictOrthogonal (booleanActiveCore q (m * q i)) (c i)

omit [LinearOrder ι] in
lemma reduceFirstHitKernels_normalized (q : ι → ℝ) (m : ℝ)
    (c : ι → Finset ι → ℝ) (hc : ∀ i, (∑ Q : Finset ι, c i Q) = 1) :
    ∀ i, (∑ Q : Finset ι, reduceFirstHitKernels q m c i Q) = 1 := by
  intro i
  rw [reduceFirstHitKernels, restrictOrthogonal_sum, hc]

/-- The reduced kernels remain prior-supported, and every retained coordinate
has expected joint hit mass strictly greater than one. -/
lemma reduceFirstHitKernels_support (q : ι → ℝ) (m : ℝ)
    (c : ι → Finset ι → ℝ) (hc : ∀ i Q, c i Q ≠ 0 → ∀ j ∈ Q, j < i) :
    ∀ i Q, reduceFirstHitKernels q m c i Q ≠ 0 →
      ∀ j ∈ Q, j < i ∧ 1 < (m * q i) * q j := by
  intro i Q hQ j hj
  obtain ⟨R, hR, he⟩ := restrictOrthogonal_nonzero _ _ Q hQ
  rw [← he, mem_inter] at hj
  exact ⟨hc i R hR j hj.1, (mem_filter.mp hj.2).2⟩

omit [LinearOrder ι] in
/-- The entire first-hit objective is no larger after the explicit reduction. -/
theorem reduceFirstHitKernels_objective_le (q : ι → ℝ) (m : ℝ)
    (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1) (hm : 0 ≤ m) (c : ι → Finset ι → ℝ) :
    (∑ i, booleanKernelObjective q (m * q i) (reduceFirstHitKernels q m c i)) ≤
      ∑ i, booleanKernelObjective q (m * q i) (c i) := by
  apply sum_le_sum
  intro i hi
  exact booleanKernelObjective_restrict_le q (m * q i) hq (mul_nonneg hm (hq i).1)
    _ (activeCore_small q (m * q i)) _

/-- For primes, only pairs with p_i*p_j < m can remain in a first-hit kernel. -/
theorem reduceFirstHitKernels_prime_support (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (m : ℕ) (c : ι → Finset ι → ℝ)
    (hc : ∀ i Q, c i Q ≠ 0 → ∀ j ∈ Q, j < i) :
    ∀ i Q, reduceFirstHitKernels (fun j => 1 / (p j : ℝ)) m c i Q ≠ 0 →
      ∀ j ∈ Q, j < i ∧ p i * p j < m := by
  intro i Q hQ j hj
  obtain ⟨hji, hprod⟩ := reduceFirstHitKernels_support _ m c hc i Q hQ j hj
  refine ⟨hji, ?_⟩
  have hi0 : (0 : ℝ) < p i := by exact_mod_cast (hp i).pos
  have hj0 : (0 : ℝ) < p j := by exact_mod_cast (hp j).pos
  have hh : (1 : ℝ) < (m / (p i : ℝ)) / (p j : ℝ) := by
    simpa only [mul_one_div] using hprod
  have h1 := (lt_div_iff₀ hj0).mp hh
  rw [one_mul] at h1
  have h2 := (lt_div_iff₀ hi0).mp h1
  have h3 : (p i : ℝ) * p j < m := by simpa only [mul_comm] using h2
  exact_mod_cast h3


/-- A lossless normal form for the entire first-hit criterion, not merely for
one fixed candidate: all useful pairwise expected hit masses can exceed one. -/
theorem firstHit_candidate_iff_reduced (q : ι → ℝ) (m : ℝ)
    (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1) (hm : 0 ≤ m) :
    (∃ c : ι → Finset ι → ℝ,
      (∀ i, (∑ Q : Finset ι, c i Q) = 1) ∧
      (∀ i Q, c i Q ≠ 0 → ∀ j ∈ Q, j < i) ∧
      (∑ i, booleanKernelObjective q (m * q i) (c i)) < m) ↔
    (∃ c : ι → Finset ι → ℝ,
      (∀ i, (∑ Q : Finset ι, c i Q) = 1) ∧
      (∀ i Q, c i Q ≠ 0 → ∀ j ∈ Q, j < i ∧ 1 < (m * q i) * q j) ∧
      (∑ i, booleanKernelObjective q (m * q i) (c i)) < m) := by
  constructor
  · rintro ⟨c, hc, hprior, hobj⟩
    refine ⟨reduceFirstHitKernels q m c,
      reduceFirstHitKernels_normalized q m c hc,
      reduceFirstHitKernels_support q m c hprior, ?_⟩
    exact (reduceFirstHitKernels_objective_le q m hq hm c).trans_lt hobj
  · rintro ⟨c, hc, hprior, hobj⟩
    exact ⟨c, hc, fun i Q hQ j hj => (hprior i Q hQ j hj).1, hobj⟩

/-- Prime formulation: forbidding kernel coordinates with p_i*p_j >= m loses
no successful first-hit Boolean-cost certificate. -/
theorem prime_firstHit_candidate_iff_reduced (p : ι → ℕ)
    (hp : ∀ i, (p i).Prime) (m : ℕ) :
    (∃ c : ι → Finset ι → ℝ,
      (∀ i, (∑ Q : Finset ι, c i Q) = 1) ∧
      (∀ i Q, c i Q ≠ 0 → ∀ j ∈ Q, j < i) ∧
      (∑ i, booleanKernelObjective (fun j => 1 / (p j : ℝ))
        ((m : ℝ) * (1 / (p i : ℝ))) (c i)) < m) ↔
    (∃ c : ι → Finset ι → ℝ,
      (∀ i, (∑ Q : Finset ι, c i Q) = 1) ∧
      (∀ i Q, c i Q ≠ 0 → ∀ j ∈ Q, j < i ∧ p i * p j < m) ∧
      (∑ i, booleanKernelObjective (fun j => 1 / (p j : ℝ))
        ((m : ℝ) * (1 / (p i : ℝ))) (c i)) < m) := by
  constructor
  · rintro ⟨c, hc, hprior, hobj⟩
    let q : ι → ℝ := fun j => 1 / (p j : ℝ)
    have hq (i : ι) : 0 ≤ q i ∧ q i ≤ 1 := by
      have hp1 : (1 : ℝ) ≤ p i := by exact_mod_cast (hp i).one_le
      exact ⟨by dsimp [q]; positivity, (div_le_one (by positivity)).mpr hp1⟩
    refine ⟨reduceFirstHitKernels q m c,
      reduceFirstHitKernels_normalized q m c hc,
      reduceFirstHitKernels_prime_support p hp m c hprior, ?_⟩
    exact (reduceFirstHitKernels_objective_le q m hq (by positivity) c).trans_lt hobj
  · rintro ⟨c, hc, hprior, hobj⟩
    exact ⟨c, hc, fun i Q hQ j hj => (hprior i Q hQ j hj).1, hobj⟩

end Ordered
#print axioms booleanKernelObjective_restrict_le
#print axioms reduceFirstHitKernels_support
#print axioms reduceFirstHitKernels_objective_le
#print axioms reduceFirstHitKernels_prime_support
#print axioms prime_firstHit_candidate_iff_reduced
end Erdos970.FiniteSelberg
