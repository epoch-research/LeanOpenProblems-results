import Submission.BooleanCoupledDuality

/-!
Exact Boolean coefficient cost of extending a common core polynomial over
omitted coordinates. The omitted-coordinate factor is exact in this class,
not a loss from applying the triangle inequality. No universal obstruction to
other kernels or to the quadratic Jacobsthal conjecture is asserted.
-/
namespace Erdos970.FiniteSelberg
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Extend a core coefficient list by subtracting each omitted hit times one
common core coefficient list. -/
noncomputable def commonTailCoefficient (S : Finset ι)
    (a b : Finset ι → ℝ) (T : Finset ι) : ℝ :=
  a T - ∑ i ∈ univ \ S, hitShiftCoefficient i b T

lemma core_coefficient_zero_of_mem_outside (S : Finset ι) (b : Finset ι → ℝ)
    (hb : ∀ T, b T ≠ 0 → T ⊆ S) (i : ι) (hi : i ∉ S)
    (T : Finset ι) (hiT : i ∈ T) : b T = 0 := by
  by_contra h
  exact hi (hb T h hiT)

lemma common_tail_shift_disjoint (S : Finset ι) (b : Finset ι → ℝ)
    (hb : ∀ T, b T ≠ 0 → T ⊆ S) (i j : ι) (hi : i ∉ S) (hj : j ∉ S)
    (hij : i ≠ j) (T : Finset ι) :
    hitShiftCoefficient i b T = 0 ∨ hitShiftCoefficient j b T = 0 := by
  by_contra h
  push_neg at h
  have hiT : i ∈ T := by
    by_contra hn
    exact h.1 (by simp [hitShiftCoefficient, hn])
  have hjT : j ∈ T := by
    by_contra hn
    exact h.2 (by simp [hitShiftCoefficient, hn])
  have hbT : b (T.erase i) ≠ 0 := by simpa only [hitShiftCoefficient, if_pos hiT] using h.1
  exact hj (hb (T.erase i) hbT (mem_erase.mpr ⟨hij.symm, hjT⟩))

lemma core_tail_disjoint (S : Finset ι) (a : Finset ι → ℝ)
    (ha : ∀ T, a T ≠ 0 → T ⊆ S) (b : Finset ι → ℝ)
    (i : ι) (hi : i ∉ S) (T : Finset ι) :
    a T = 0 ∨ hitShiftCoefficient i b T = 0 := by
  by_cases h : a T = 0
  · exact Or.inl h
  · right
    have hiT : i ∉ T := fun hh => hi (ha T h hh)
    simp [hitShiftCoefficient, hiT]

/-- At every monomial, at most one omitted-coordinate shift can occur, and
  any such shift has zero core coefficient. -/
lemma commonTailCoefficient_abs (S : Finset ι) (a b : Finset ι → ℝ)
    (ha : ∀ T, a T ≠ 0 → T ⊆ S) (hb : ∀ T, b T ≠ 0 → T ⊆ S)
    (T : Finset ι) :
    |commonTailCoefficient S a b T| = |a T| + ∑ i ∈ univ \ S, |hitShiftCoefficient i b T| := by
  classical
  by_cases hex : ∃ i ∈ univ \ S, hitShiftCoefficient i b T ≠ 0
  · obtain ⟨i, hi, hne⟩ := hex
    have hiS : i ∉ S := (mem_sdiff.mp hi).2
    have haz : a T = 0 := (core_tail_disjoint S a ha b i hiS T).resolve_right hne
    have hz (j : ι) (hj : j ∈ univ \ S) (hji : j ≠ i) : hitShiftCoefficient j b T = 0 :=
      (common_tail_shift_disjoint S b hb j i (mem_sdiff.mp hj).2 hiS hji T).resolve_right hne
    unfold commonTailCoefficient
    rw [sum_eq_single i (fun j hj hji => hz j hj hji) (by simp [hi]),
      sum_eq_single i (fun j hj hji => by rw [hz j hj hji, abs_zero]) (by simp [hi]),
      haz, abs_zero, zero_sub, abs_neg, zero_add]
  · push_neg at hex
    have hz : (∑ i ∈ univ \ S, hitShiftCoefficient i b T) = 0 :=
      sum_eq_zero (fun i hi => hex i hi)
    have hza : (∑ i ∈ univ \ S, |hitShiftCoefficient i b T|) = 0 :=
      sum_eq_zero (fun i hi => by rw [hex i hi, abs_zero])
    simp only [commonTailCoefficient, hz, hza, sub_zero, add_zero]

/-- Exact cost identity for the whole common-kernel extension. In particular,
  the omitted-coordinate count is not removed by Boolean coefficient merging. -/
theorem commonTailCoefficient_cost (S : Finset ι) (a b : Finset ι → ℝ)
    (ha : ∀ T, a T ≠ 0 → T ⊆ S) (hb : ∀ T, b T ≠ 0 → T ⊆ S) :
    (∑ T : Finset ι, |commonTailCoefficient S a b T|) =
      (∑ T : Finset ι, |a T|) + ((univ \ S).card : ℝ) * ∑ T : Finset ι, |b T| := by
  simp_rw [commonTailCoefficient_abs S a b ha hb]
  rw [sum_add_distrib, sum_comm]
  have he (i : ι) (hi : i ∈ univ \ S) :
      (∑ T : Finset ι, |hitShiftCoefficient i b T|) = ∑ T : Finset ι, |b T| := by
    apply hitShift_cost
    intro T hiT
    exact core_coefficient_zero_of_mem_outside S b hb i (mem_sdiff.mp hi).2 T hiT
  congr 1
  calc
    _ = ∑ i ∈ univ \ S, (∑ T : Finset ι, |b T|) := by
      apply sum_congr rfl
      intro i hi
      exact he i hi
    _ = _ := by simp

/-- The coefficient extension is the desired common-core polynomial minus
  the sum of omitted hits multiplied by the common core polynomial. -/
theorem commonTailCoefficient_value (S : Finset ι) (a b : Finset ι → ℝ)
    (hb : ∀ T, b T ≠ 0 → T ⊆ S) (ω : ι → Bool) :
    booleanValue (commonTailCoefficient S a b) ω =
      booleanValue a ω - (∑ i ∈ univ \ S, hitMonomial {i} ω) * booleanValue b ω := by
  unfold booleanValue commonTailCoefficient
  simp only [sub_mul, sum_sub_distrib, sum_mul]
  rw [sum_comm]
  congr 1
  apply sum_congr rfl
  intro i hi
  exact hitShift_expansion i b (fun T hiT =>
    core_coefficient_zero_of_mem_outside S b hb i (mem_sdiff.mp hi).2 T hiT) ω

/-- The full cost is at least the omitted-coordinate count times the common
  coefficient cost. No lower estimate on that latter cost is assumed here. -/
theorem commonTailCoefficient_cost_lower (S : Finset ι) (a b : Finset ι → ℝ)
    (ha : ∀ T, a T ≠ 0 → T ⊆ S) (hb : ∀ T, b T ≠ 0 → T ⊆ S) :
    ((univ \ S).card : ℝ) * (∑ T : Finset ι, |b T|) ≤
      ∑ T : Finset ι, |commonTailCoefficient S a b T| := by
  rw [commonTailCoefficient_cost S a b ha hb]
  exact le_add_of_nonneg_left (sum_nonneg (fun _ _ => abs_nonneg _))

/-- Boolean multiplication by a hit, without any support restriction. -/
noncomputable def hitProductCoefficient (i : ι) (b : Finset ι → ℝ)
    (T : Finset ι) : ℝ :=
  if i ∈ T then b T + b (T.erase i) else 0

lemma hitProduct_expansion (i : ι) (b : Finset ι → ℝ) (ω : ι → Bool) :
    booleanValue (hitProductCoefficient i b) ω =
      hitMonomial {i} ω * booleanValue b ω := by
  unfold booleanValue
  rw [sum_all_split i, sum_all_split i (fun T => b T * hitMonomial T ω), mul_sum]
  apply sum_congr rfl
  intro Q hQ
  have hiQ := not_mem_of_erase_powerset hQ
  simp only [hitProductCoefficient, if_neg hiQ, mem_insert_self, if_true,
    erase_insert hiQ, zero_mul, zero_add]
  rw [show insert i Q = {i} ∪ Q by simp, ← hitMonomial_mul]
  simp only [singleton_union]
  have hx : hitMonomial {i} ω * hitMonomial {i} ω = hitMonomial {i} ω := by
    rw [hitMonomial_mul, union_self]
  calc
    _ = b (insert i Q) * (hitMonomial {i} ω * hitMonomial {i} ω) * hitMonomial Q ω +
        hitMonomial {i} ω * (b Q * hitMonomial Q ω) := by rw [hx]; ring
    _ = _ := by ring

/-- Core part of the common lower polynomial `(1 - totalHits) * b`. -/
noncomputable def coreLowerCoefficient (S : Finset ι) (b : Finset ι → ℝ)
    (T : Finset ι) : ℝ := b T - ∑ i ∈ S, hitProductCoefficient i b T

lemma hitProduct_supported (S : Finset ι) (b : Finset ι → ℝ)
    (hb : ∀ T, b T ≠ 0 → T ⊆ S) (i : ι) (hi : i ∈ S)
    (T : Finset ι) (hT : hitProductCoefficient i b T ≠ 0) : T ⊆ S := by
  by_cases hiT : i ∈ T
  · have hh : b T ≠ 0 ∨ b (T.erase i) ≠ 0 := by
      by_contra hn
      push_neg at hn
      exact hT (by simp [hitProductCoefficient, hiT, hn])
    rcases hh with hh | hh
    · exact hb T hh
    · intro j hj
      by_cases hji : j = i
      · exact hji ▸ hi
      · exact hb (T.erase i) hh (mem_erase.mpr ⟨hji, hj⟩)
  · exact False.elim (hT (by simp [hitProductCoefficient, hiT]))

lemma coreLower_supported (S : Finset ι) (b : Finset ι → ℝ)
    (hb : ∀ T, b T ≠ 0 → T ⊆ S) (T : Finset ι)
    (hT : coreLowerCoefficient S b T ≠ 0) : T ⊆ S := by
  by_contra hn
  have hz : b T = 0 := by by_contra h; exact hn (hb T h)
  have hs : (∑ i ∈ S, hitProductCoefficient i b T) = 0 := by
    apply sum_eq_zero
    intro i hi
    by_contra h
    exact hn (hitProduct_supported S b hb i hi T h)
  exact hT (by simp [coreLowerCoefficient, hz, hs])

lemma coreLower_value (S : Finset ι) (b : Finset ι → ℝ) (ω : ι → Bool) :
    booleanValue (coreLowerCoefficient S b) ω =
      (1 - ∑ i ∈ S, hitMonomial {i} ω) * booleanValue b ω := by
  unfold booleanValue coreLowerCoefficient
  simp only [sub_mul, sum_sub_distrib, sum_mul, one_mul]
  rw [sum_comm]
  congr 1
  apply sum_congr rfl
  intro i hi
  exact hitProduct_expansion i b ω

/-- The standard common lower weight, with its coefficient cost reduced
exactly in the Boolean polynomial basis. -/
noncomputable def commonLowerCoefficient (S : Finset ι) (b : Finset ι → ℝ) :
    Finset ι → ℝ := commonTailCoefficient S (coreLowerCoefficient S b) b

lemma commonLower_value (S : Finset ι) (b : Finset ι → ℝ)
    (hb : ∀ T, b T ≠ 0 → T ⊆ S) (ω : ι → Bool) :
    booleanValue (commonLowerCoefficient S b) ω =
      (1 - ∑ i, hitMonomial {i} ω) * booleanValue b ω := by
  rw [commonLowerCoefficient, commonTailCoefficient_value S _ b hb, coreLower_value]
  have hsum := sum_sdiff (s₁ := S) (s₂ := univ) (subset_univ S)
    (f := fun i => hitMonomial {i} ω)
  rw [← hsum]; ring

/-- The omitted-coordinate factor survives exact coefficient merging for the
standard common lower polynomial. This is not a lower bound on the core cost. -/
theorem commonLower_cost (S : Finset ι) (b : Finset ι → ℝ)
    (hb : ∀ T, b T ≠ 0 → T ⊆ S) :
    (∑ T : Finset ι, |commonLowerCoefficient S b T|) =
      (∑ T : Finset ι, |coreLowerCoefficient S b T|) +
        ((univ \ S).card : ℝ) * ∑ T : Finset ι, |b T| :=
  commonTailCoefficient_cost S _ b (coreLower_supported S b hb) hb

lemma ordinaryCoefficient_supported (S : Finset ι) (q : ι → ℝ)
    (c : Finset ι → ℝ) (hc : ∀ T, c T ≠ 0 → T ⊆ S)
    (T : Finset ι) (hT : ordinaryCoefficient q c T ≠ 0) : T ⊆ S := by
  by_contra hn
  apply hT
  unfold ordinaryCoefficient
  have hz : (∑ Q : Finset ι, if T ⊆ Q then c Q else 0) = 0 := by
    apply sum_eq_zero
    intro Q hQ
    by_cases hTQ : T ⊆ Q
    · have hzero : c Q = 0 := by
        by_contra h
        exact hn (hTQ.trans (hc Q h))
      simp [hzero]
    · simp [hTQ]
  rw [hz, mul_zero]

lemma booleanSquareCoefficient_supported (S : Finset ι) (a : Finset ι → ℝ)
    (ha : ∀ Q, a Q ≠ 0 → Q ⊆ S) (T : Finset ι)
    (hT : booleanSquareCoefficient a T ≠ 0) : T ⊆ S := by
  obtain ⟨Q, _, hQ⟩ := exists_ne_zero_of_sum_ne_zero hT
  obtain ⟨R, _, hR⟩ := exists_ne_zero_of_sum_ne_zero hQ
  by_cases he : Q ∪ R = T
  · rw [if_pos he] at hR
    obtain ⟨haQ, haR⟩ := mul_ne_zero_iff.mp hR
    rw [← he]
    exact union_subset (ha Q haQ) (ha R haR)
  · simp [he] at hR

/-- Specialization to a common square kernel supported on the core. -/
theorem commonLower_square_cost (S : Finset ι) (q : ι → ℝ)
    (c : Finset ι → ℝ) (hc : ∀ T, c T ≠ 0 → T ⊆ S) :
    (∑ T : Finset ι, |commonLowerCoefficient S
        (booleanSquareCoefficient (ordinaryCoefficient q c)) T|) =
      (∑ T : Finset ι, |coreLowerCoefficient S
        (booleanSquareCoefficient (ordinaryCoefficient q c)) T|) +
      ((univ \ S).card : ℝ) * booleanSquareCost (ordinaryCoefficient q c) :=
  commonLower_cost S _ (booleanSquareCoefficient_supported S _
    (ordinaryCoefficient_supported S q c hc))

#print axioms commonLower_value
#print axioms commonLower_square_cost

#print axioms commonTailCoefficient_cost
#print axioms commonTailCoefficient_value
#print axioms commonTailCoefficient_cost_lower
end Erdos970.FiniteSelberg
