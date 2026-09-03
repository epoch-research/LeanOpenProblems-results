import Submission.CoreFilteredSelberg
import Submission.SoftExposureSymmetric

/-! A limitation of combining the exact soft-exposure budget with deletion
cylinders. A retained core of at least the exposure depth already has a cylinder
weight no larger than that budget. A smaller core falls under the deterministic
partial-count premise, so a filtered-budget contradiction in that case needs no
probabilistic tail estimate. This is not an obstruction to other lower-tail
estimates, and is not a disproof of the quadratic Jacobsthal conjecture. -/
namespace Erdos970.SoftExposure
open Finset Real GapAverages

lemma reciprocal_product_antitone (Q T : Finset ℕ) (hTQ : T ⊆ Q)
    (hQ : ∀ q ∈ Q, q.Prime) :
    (∏ q ∈ Q, (q : ℝ)⁻¹) ≤ ∏ q ∈ T, (q : ℝ)⁻¹ := by
  classical
  rw [← prod_sdiff hTQ]
  apply mul_le_of_le_one_left (prod_nonneg (fun q _ => by positivity))
  apply prod_le_one (fun q _ => by positivity)
  intro q hq
  apply inv_le_one_of_one_le₀
  exact_mod_cast (hQ q (mem_sdiff.mp hq).1).one_le

/-- The exposure budget contains every j-element retained subcore, with its
factorial multiplicity. Further retained primes only decrease cylinder weight. -/
theorem factorial_cylinder_weight_le_budget (P Q : Finset ℕ) (hQP : Q ⊆ P)
    (hP : ∀ p ∈ P, p.Prime) (j : ℕ) (hjQ : j ≤ Q.card) :
    (j.factorial : ℝ) * (∏ q ∈ Q, (q : ℝ)⁻¹) ≤ budget j P := by
  classical
  obtain ⟨T, hTQ, hTj⟩ := exists_subset_card_eq hjQ
  have hTP : T ⊆ P := hTQ.trans hQP
  have hprod := reciprocal_product_antitone Q T hTQ (fun q hq => hP q (hQP hq))
  have hsum : (∏ q ∈ T, (q : ℝ)⁻¹) ≤
      ∑ U ∈ P.powersetCard j, ∏ q ∈ U, (q : ℝ)⁻¹ :=
    single_le_sum (f := fun U : Finset ℕ => ∏ q ∈ U, (q : ℝ)⁻¹)
      (fun U _ => prod_nonneg (fun q _ => by positivity))
      (mem_powersetCard.mpr ⟨hTP, hTj⟩)
  rw [budget_eq_factorial_symmetric]
  exact mul_le_mul_of_nonneg_left (hprod.trans hsum) (Nat.cast_nonneg _)

/-- For a retained core at least as large as the depth, the exact soft-exposure
upper bound cannot be strictly less than the cylinder's probability. -/
theorem cylinder_weight_le_scaled_budget (P Q : Finset ℕ) (hQP : Q ⊆ P)
    (hP : ∀ p ∈ P, p.Prime) (j : ℕ) (hjQ : j ≤ Q.card)
    (A b : ℝ) (hA : 0 < A) (hb : 0 ≤ b) (hbA : b < A) :
    (∏ q ∈ Q, (q : ℝ)⁻¹) ≤ budget j P / (1 - b / A) ^ j := by
  have hprod : 0 ≤ ∏ q ∈ Q, (q : ℝ)⁻¹ := prod_nonneg (fun q _ => by positivity)
  have hfac : (1 : ℝ) ≤ j.factorial := by exact_mod_cast Nat.factorial_pos j
  have hh := (mul_le_mul_of_nonneg_right hfac hprod).trans
    (factorial_cylinder_weight_le_budget P Q hQP hP j hjQ)
  simp only [one_mul] at hh
  have hbase : 0 < 1 - b / A := sub_pos.mpr ((div_lt_one hA).mpr hbA)
  have hbase1 : 1 - b / A ≤ 1 := by have := div_nonneg hb hA.le; linarith
  apply (le_div_iff₀ (pow_pos hbase j)).mpr
  exact (mul_le_of_le_one_right hprod (pow_le_one₀ hbase.le hbase1)).trans hh

lemma partial_survivors_eq_core (P Q : Finset ℕ) (hQP : Q ⊆ P)
    (m : ℕ) (r : Phase P) :
    survivors (range m) Q (phaseResidues P r) =
      CoverFibers.phaseSurvivors Q m (corePhase P Q hQP r) := by
  classical
  ext x
  simp only [survivors, CoverFibers.phaseSurvivors, mem_filter]
  apply and_congr_right
  intro _
  constructor
  · intro hh q hhit
    apply hh q.val q.property
    change x % q.val = phaseResidues P r q.val % q.val
    rw [phaseResidues_mem P r ⟨q.val, hQP q.property⟩,
      Nat.mod_eq_of_lt (r ⟨q.val, hQP q.property⟩).isLt]
    exact hhit
  · intro hh q hq hhit
    apply hh ⟨q, hq⟩
    change x % q = phaseResidues P r q % q at hhit
    rw [phaseResidues_mem P r ⟨q, hQP hq⟩,
      Nat.mod_eq_of_lt (r ⟨q, hQP hq⟩).isLt] at hhit
    exact hhit

/-- Below the exposure depth the core already has the deterministic lower
count, independently of the averaged soft-exposure argument. -/
lemma partial_lower_core_count (P Q : Finset ℕ) (hQP : Q ⊆ P)
    (m j : ℕ) (A : ℝ) (r : Phase P)
    (hpartial : PartialLower j (range m) P (phaseResidues P r) A)
    (hQj : Q.card < j) : A ≤ intervalCount Q m (corePhase P Q hQP r) := by
  have hh := hpartial Q hQP hQj
  rwa [partial_survivors_eq_core P Q hQP m r, CoverFibers.phaseSurvivors_card] at hh

/-- Any covered phase whose filtered budget lies below the partial-count floor
must retain at least j coordinates. -/
theorem depth_le_core_card_of_filtered_cover (P Q : Finset ℕ) (hQP : Q ⊆ P)
    (m j : ℕ) (A b : ℝ) (hbA : b < A) (r : Phase P)
    (hpartial : PartialLower j (range m) P (phaseResidues P r) A)
    (hr : intervalCount P m r = 0)
    (hB : filteredDeletionBudget P Q hQP m r ≤ b) : j ≤ Q.card := by
  by_contra hn
  have hl := partial_lower_core_count P Q hQP m j A r hpartial (by omega)
  exact hbA.not_ge (hl.trans ((core_count_le_filteredDeletionBudget P Q hQP m r hr).trans hB))

/-- For a small core the deterministic row comparison already excludes the
cover; no estimate on phase probability is required. -/
theorem no_cover_of_small_core_filtered_budget (P Q : Finset ℕ) (hQP : Q ⊆ P)
    (m j : ℕ) (A b : ℝ) (hbA : b < A) (r : Phase P)
    (hpartial : PartialLower j (range m) P (phaseResidues P r) A)
    (hQj : Q.card < j) (hB : filteredDeletionBudget P Q hQP m r ≤ b) :
    intervalCount P m r ≠ 0 := by
  intro hr
  exact hQj.not_ge (depth_le_core_card_of_filtered_cover P Q hQP m j A b hbA r hpartial hr hB)

#print axioms factorial_cylinder_weight_le_budget
#print axioms cylinder_weight_le_scaled_budget
#print axioms depth_le_core_card_of_filtered_cover
#print axioms no_cover_of_small_core_filtered_budget
end Erdos970.SoftExposure
