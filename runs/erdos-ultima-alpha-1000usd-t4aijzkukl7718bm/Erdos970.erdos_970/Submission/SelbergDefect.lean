import Submission.SelbergLowerCriterion

/-! A subset-size formula for the exact Selberg lower-sieve main term. -/
namespace Erdos970.FiniteSelberg

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem weight_insert (q : ι → ℝ) (Q : Finset ι) (i : ι) (hi : i ∉ Q) :
    weight q (insert i Q) = (q i / (1 - q i)) * weight q Q := by
  simp only [weight, Finset.prod_insert hi]

/-- Inserting a coordinate bijects the paired part of a downset with its members
containing that coordinate. -/
theorem weight_containing_eq (q : ι → ℝ) (D : Finset (Finset ι))
    (hD : ∀ A ∈ D, ∀ B ⊆ A, B ∈ D) (i : ι) :
    (∑ Q ∈ D, if i ∈ Q then weight q Q else 0) =
      (q i / (1 - q i)) *
        ∑ Q ∈ D, if i ∉ Q ∧ insert i Q ∈ D then weight q Q else 0 := by
  classical
  rw [← Finset.sum_filter, ← Finset.sum_filter, Finset.mul_sum]
  symm
  apply Finset.sum_bij (fun Q hQ => insert i Q)
  · intro Q hQ
    have hh := Finset.mem_filter.mp hQ
    exact Finset.mem_filter.mpr ⟨hh.2.2, Finset.mem_insert_self _ _⟩
  · intro A hA B hB hAB
    have hAi := (Finset.mem_filter.mp hA).2.1
    have hBi := (Finset.mem_filter.mp hB).2.1
    have hh := congrArg (fun Q : Finset ι => Q.erase i) hAB
    simpa [hAi, hBi] using hh
  · intro Q hQ
    have hh := Finset.mem_filter.mp hQ
    refine ⟨Q.erase i, Finset.mem_filter.mpr ⟨hD Q hh.1 _ (Finset.erase_subset i Q), ?_⟩, ?_⟩
    · exact ⟨Finset.notMem_erase i Q, by simpa [Finset.insert_erase hh.2] using hh.1⟩
    · exact Finset.insert_erase hh.2
  · intro Q hQ
    exact (weight_insert q Q i (Finset.mem_filter.mp hQ).2.1).symm

/-- One-coordinate boundary mass is the corresponding marginal deficit. -/
theorem coordinate_boundary_eq (q : ι → ℝ) (hq : ∀ i, 0 < q i ∧ q i < 1)
    (D : Finset (Finset ι)) (hD : ∀ A ∈ D, ∀ B ⊆ A, B ∈ D) (i : ι) :
    q i * normalizer q (insertionBoundary D i) =
      q i * normalizer q D - ∑ Q ∈ D, if i ∈ Q then weight q Q else 0 := by
  classical
  let A := ∑ Q ∈ D, if i ∈ Q then weight q Q else 0
  let B := ∑ Q ∈ D, if i ∉ Q ∧ insert i Q ∈ D then weight q Q else 0
  let C := ∑ Q ∈ D, if i ∉ Q ∧ insert i Q ∉ D then weight q Q else 0
  have hA : A = q i / (1 - q i) * B := weight_containing_eq q D hD i
  have hG : normalizer q D = A + B + C := by
    simp only [normalizer, ← weight_eq_inverse_variance, A, B, C, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro Q hQ
    by_cases hi : i ∈ Q <;> by_cases hQi : insert i Q ∈ D <;> simp [hi, hQi]
  have hC : normalizer q (insertionBoundary D i) = C := by
    simp only [normalizer, insertionBoundary, Finset.sum_filter, ← weight_eq_inverse_variance, C]
  change q i * normalizer q (insertionBoundary D i) = q i * normalizer q D - A
  rw [hC, hG, hA]
  have hqi : 1 - q i ≠ 0 := (sub_pos.mpr (hq i).2).ne'
  field_simp
  ring

/-- The boundary-defect numerator depends only on the weighted subset-size distribution. -/
theorem boundaryDefect_eq_card_sum (q : ι → ℝ) (hq : ∀ i, 0 < q i ∧ q i < 1)
    (D : Finset (Finset ι)) (hD : ∀ A ∈ D, ∀ B ⊆ A, B ∈ D) :
    boundaryDefect q D =
      (1 - ∑ i, q i) * normalizer q D + ∑ Q ∈ D, (Q.card : ℝ) * weight q Q := by
  classical
  unfold boundaryDefect
  simp_rw [coordinate_boundary_eq q hq D hD]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, Finset.sum_comm]
  have hc (Q : Finset ι) :
      (∑ i : ι, if i ∈ Q then weight q Q else 0) = (Q.card : ℝ) * weight q Q := by
    simp
  simp_rw [hc]
  ring

/-- A useful purely finite positivity test, with no interval estimate hidden in the statement. -/
theorem boundaryDefect_pos_iff (q : ι → ℝ) (hq : ∀ i, 0 < q i ∧ q i < 1)
    (D : Finset (Finset ι)) (hDn : D.Nonempty)
    (hD : ∀ A ∈ D, ∀ B ⊆ A, B ∈ D) :
    0 < boundaryDefect q D ↔
      (∑ i, q i) - 1 < (∑ Q ∈ D, (Q.card : ℝ) * weight q Q) / normalizer q D := by
  rw [boundaryDefect_eq_card_sum q hq D hD,
    lt_div_iff₀ (normalizer_pos q hq D hDn)]
  constructor <;> intro hh <;> nlinarith

/-- In particular, positive main term is impossible when every supported set is too small. -/
theorem boundaryDefect_nonpos_of_card_bound (q : ι → ℝ) (hq : ∀ i, 0 < q i ∧ q i < 1)
    (D : Finset (Finset ι)) (hD : ∀ A ∈ D, ∀ B ⊆ A, B ∈ D)
    (t : ℕ) (ht : ∀ Q ∈ D, Q.card ≤ t) (hmass : (t : ℝ) + 1 ≤ ∑ i, q i) :
    boundaryDefect q D ≤ 0 := by
  rw [boundaryDefect_eq_card_sum q hq D hD]
  have hcard : (∑ Q ∈ D, (Q.card : ℝ) * weight q Q) ≤ (t : ℝ) * normalizer q D := by
    simp only [normalizer, ← weight_eq_inverse_variance, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro Q hQ
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast ht Q hQ) (weight_pos q hq Q).le
  have hG : 0 ≤ normalizer q D := by
    unfold normalizer
    exact Finset.sum_nonneg (fun Q hQ => (one_div_pos.mpr (variance_pos q hq Q)).le)
  nlinarith

#print axioms boundaryDefect_eq_card_sum
#print axioms boundaryDefect_pos_iff
#print axioms boundaryDefect_nonpos_of_card_bound

end Erdos970.FiniteSelberg
