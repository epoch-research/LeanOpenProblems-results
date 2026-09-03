import Submission.SelbergNormalizer

/-! A finite Selberg lower weight and its exact boundary-defect mean. -/
namespace Erdos970.FiniteSelberg

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem average_sub (q : ι → ℝ) (f g : (ι → Bool) → ℝ) :
    average q (fun ω => f ω - g ω) = average q f - average q g := by
  simp only [average, mul_sub, Finset.sum_sub_distrib]

theorem basis_eq_prod (q : ι → ℝ) (Q : Finset ι) (ω : ι → Bool) :
    basis q Q ω = ∏ i ∈ Q, contrast (q i) (ω i) := by
  simp [basis, Finset.prod_ite_mem]

theorem basis_insert (q : ι → ℝ) (Q : Finset ι) (i : ι) (hi : i ∉ Q) (ω : ι → Bool) :
    basis q (insert i Q) ω = contrast (q i) (ω i) * basis q Q ω := by
  simp only [basis_eq_prod, Finset.prod_insert hi]

/-- The unnormalized kernel reproduces evaluation at the empty hit pattern. -/
theorem average_kernel_basis (q : ι → ℝ) (hq : ∀ i, 0 < q i ∧ q i < 1)
    (D : Finset (Finset ι)) (Q : Finset ι) :
    average q (fun ω => kernel q D ω * basis q Q ω) = if Q ∈ D then 1 else 0 := by
  classical
  have heq : (fun ω => kernel q D ω * basis q Q ω) =
      fun ω => ∑ R ∈ D, (1 / variance q R) * (basis q R ω * basis q Q ω) := by
    funext ω
    simp only [kernel, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro R hR
    ring
  rw [heq, average_sum]
  simp_rw [average_mul_const, average_basis_mul q (fun i => (hq i).1.ne')]
  have hh (R : Finset ι) : (1 / variance q R) * (if R = Q then variance q R else 0) =
      if R = Q then 1 else 0 := by
    by_cases hRQ : R = Q
    · simp only [if_pos hRQ, one_div_mul_cancel (variance_pos q hq R).ne']
    · simp only [if_neg hRQ, mul_zero]
  simp_rw [hh]
  simp

noncomputable def hitCoordinate (i : ι) (ω : ι → Bool) : ℝ := if ω i then 1 else 0

theorem hitCoordinate_mul_contrast (q : ℝ) (hq : q ≠ 0) (b : Bool) :
    (if b then (1 : ℝ) else 0) * contrast q b = (1 - q) * (contrast q b - 1) := by
  cases b <;> simp only [contrast, Bool.false_eq_true, ↓reduceIte] <;> field_simp <;> ring

theorem hitCoordinate_eq (q : ℝ) (hq : q ≠ 0) (b : Bool) :
    (if b then (1 : ℝ) else 0) = q * (1 - contrast q b) := by
  cases b <;> simp only [contrast, Bool.false_eq_true, ↓reduceIte] <;> field_simp <;> ring

theorem hitCoordinate_mul_basis_of_mem (q : ι → ℝ) (Q : Finset ι) (i : ι)
    (hq : q i ≠ 0) (hi : i ∈ Q) (ω : ι → Bool) :
    hitCoordinate i ω * basis q Q ω =
      (1 - q i) * (basis q Q ω - basis q (Q.erase i) ω) := by
  have hb : basis q Q ω = contrast (q i) (ω i) * basis q (Q.erase i) ω := by
    rw [← Finset.insert_erase hi, basis_insert q _ i (Finset.notMem_erase i Q)]
    simp
  rw [hb]
  calc
    _ = ((if ω i then (1 : ℝ) else 0) * contrast (q i) (ω i)) * basis q (Q.erase i) ω := by
      unfold hitCoordinate
      ring
    _ = _ := by rw [hitCoordinate_mul_contrast (q i) hq]; ring

theorem hitCoordinate_mul_basis_of_not_mem (q : ι → ℝ) (Q : Finset ι) (i : ι)
    (hq : q i ≠ 0) (hi : i ∉ Q) (ω : ι → Bool) :
    hitCoordinate i ω * basis q Q ω =
      q i * (basis q Q ω - basis q (insert i Q) ω) := by
  rw [basis_insert q Q i hi]
  unfold hitCoordinate
  rw [hitCoordinate_eq (q i) hq]
  ring

/-- Only the insertion boundary of the support contributes to the hit-weighted mean. -/
theorem average_kernel_hit_basis (q : ι → ℝ) (hq : ∀ i, 0 < q i ∧ q i < 1)
    (D : Finset (Finset ι)) (hD : ∀ A ∈ D, ∀ B ⊆ A, B ∈ D)
    (Q : Finset ι) (hQ : Q ∈ D) (i : ι) :
    average q (fun ω => kernel q D ω * (hitCoordinate i ω * basis q Q ω)) =
      if i ∉ Q ∧ insert i Q ∉ D then q i else 0 := by
  classical
  by_cases hi : i ∈ Q
  · have heq : (fun ω => kernel q D ω * (hitCoordinate i ω * basis q Q ω)) =
        fun ω => (1 - q i) * (kernel q D ω * basis q Q ω -
          kernel q D ω * basis q (Q.erase i) ω) := by
      funext ω
      rw [hitCoordinate_mul_basis_of_mem q Q i (hq i).1.ne' hi]
      ring
    rw [heq, average_mul_const, average_sub]
    have hQi : Q.erase i ∈ D := hD Q hQ _ (Finset.erase_subset i Q)
    simp [average_kernel_basis q hq, hQ, hQi, hi]
  · have heq : (fun ω => kernel q D ω * (hitCoordinate i ω * basis q Q ω)) =
        fun ω => q i * (kernel q D ω * basis q Q ω -
          kernel q D ω * basis q (insert i Q) ω) := by
      funext ω
      rw [hitCoordinate_mul_basis_of_not_mem q Q i (hq i).1.ne' hi]
      ring
    rw [heq, average_mul_const, average_sub]
    by_cases hQi : insert i Q ∈ D <;> simp [average_kernel_basis q hq, hQ, hQi, hi]

noncomputable def insertionBoundary (D : Finset (Finset ι)) (i : ι) : Finset (Finset ι) :=
  D.filter (fun Q => i ∉ Q ∧ insert i Q ∉ D)

theorem kernel_square_hit_average (q : ι → ℝ) (hq : ∀ i, 0 < q i ∧ q i < 1)
    (D : Finset (Finset ι)) (hD : ∀ A ∈ D, ∀ B ⊆ A, B ∈ D) (i : ι) :
    average q (fun ω => hitCoordinate i ω * kernel q D ω ^ 2) =
      q i * normalizer q (insertionBoundary D i) := by
  classical
  have heq : (fun ω => hitCoordinate i ω * kernel q D ω ^ 2) =
      fun ω => ∑ Q ∈ D, (1 / variance q Q) *
        (kernel q D ω * (hitCoordinate i ω * basis q Q ω)) := by
    funext ω
    conv_lhs => rw [pow_two]; arg 2; arg 2; rw [kernel]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro Q hQ
    ring
  rw [heq, average_sum]
  calc
    _ = ∑ Q ∈ D, (1 / variance q Q) *
        (if i ∉ Q ∧ insert i Q ∉ D then q i else 0) := by
      apply Finset.sum_congr rfl
      intro Q hQ
      rw [average_mul_const, average_kernel_hit_basis q hq D hD Q hQ i]
    _ = _ := by
      simp only [normalizer, insertionBoundary, Finset.sum_filter, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro Q hQ
      split_ifs <;> ring

noncomputable def boundaryDefect (q : ι → ℝ) (D : Finset (Finset ι)) : ℝ :=
  normalizer q D - ∑ i, q i * normalizer q (insertionBoundary D i)

/-- A signed lower sieve obtained by penalizing every hit. -/
noncomputable def minorant (q : ι → ℝ) (D : Finset (Finset ι)) (ω : ι → Bool) : ℝ :=
  (1 - ∑ i, hitCoordinate i ω) * majorant q D ω

theorem minorant_le_indicator_empty (q : ι → ℝ) (hq : ∀ i, 0 < q i ∧ q i < 1)
    (D : Finset (Finset ι)) (hDn : D.Nonempty) (ω : ι → Bool) :
    minorant q D ω ≤ if ω = (fun _ => false) then 1 else 0 := by
  classical
  by_cases hω : ω = (fun _ => false)
  · subst ω
    simp [minorant, hitCoordinate, majorant_at_empty q hq D hDn]
  · rw [if_neg hω]
    have hex : ∃ i, ω i = true := by
      by_contra hh
      push_neg at hh
      apply hω
      funext i
      cases hi : ω i
      · rfl
      · exact (hh i hi).elim
    obtain ⟨i, hi⟩ := hex
    have hsum : 1 ≤ ∑ j, hitCoordinate j ω := by
      have hh := Finset.single_le_sum (f := fun j => hitCoordinate j ω)
        (fun j hj => by change (0 : ℝ) ≤ if ω j then 1 else 0; split_ifs <;> norm_num) (Finset.mem_univ i)
      simpa [hitCoordinate, hi] using hh
    exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hsum) (majorant_nonneg q D ω)

/-- Exact mean of the finite lower weight. Positivity is governed by a support boundary defect. -/
theorem minorant_average (q : ι → ℝ) (hq : ∀ i, 0 < q i ∧ q i < 1)
    (D : Finset (Finset ι)) (hD : ∀ A ∈ D, ∀ B ⊆ A, B ∈ D) :
    average q (minorant q D) = boundaryDefect q D / normalizer q D ^ 2 := by
  have heq : minorant q D = fun ω => (1 / normalizer q D ^ 2) *
      (kernel q D ω ^ 2 - ∑ i, hitCoordinate i ω * kernel q D ω ^ 2) := by
    funext ω
    simp only [minorant, majorant]
    rw [← Finset.sum_mul]
    ring
  rw [heq, average_mul_const, average_sub, average_sum, kernel_square_average q hq D]
  simp_rw [kernel_square_hit_average q hq D hD]
  unfold boundaryDefect
  ring

#print axioms minorant_average
#print axioms minorant_le_indicator_empty

end Erdos970.FiniteSelberg
