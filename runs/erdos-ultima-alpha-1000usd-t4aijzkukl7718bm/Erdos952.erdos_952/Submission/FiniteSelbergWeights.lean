import Submission.FiniteSelbergOptimization

/-! Explicit optimal Selberg weights and a uniform bound on their absolute
values. This controls the weights themselves, not the growth of the Selberg
denominator needed to rule out Gaussian prime paths. -/
namespace Erdos952Investigation.FiniteSelbergWeights
open FiniteSelbergOptimization
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 0

variable {ι : Type*}

lemma sign_union (s t : Finset ι) (h : Disjoint s t) : sign (s∪t) = sign s*sign t := by
  rw [sign,Finset.card_union_of_disjoint h,pow_add]
  rfl

lemma sum_sign_interval (r t : Finset ι) :
    (∑ s ∈ Finset.Icc r t, sign s) = if r = t then sign r else 0 := by
  classical
  by_cases hrt : r ⊆ t
  · rw [Finset.Icc_eq_image_powerset hrt,Finset.sum_image]
    · have he (s : Finset ι) (hs : s ∈ (t\r).powerset) : sign (r∪s) = sign r*sign s :=
        sign_union r s (Finset.disjoint_sdiff.mono_right (Finset.mem_powerset.mp hs))
      rw [Finset.sum_congr rfl he,← Finset.mul_sum,sum_sign_subsets]
      have hi : t\r = ∅ ↔ r = t := by
        rw [Finset.sdiff_eq_empty_iff_subset]
        exact ⟨fun h => Finset.Subset.antisymm hrt h,fun h => h ▸ Finset.Subset.refl _⟩
      simp only [hi]
      split_ifs <;> ring
    · intro s hs u hu he
      change r∪s = r∪u at he
      have hs' := Finset.mem_powerset.mp hs
      have hu' := Finset.mem_powerset.mp hu
      apply Finset.Subset.antisymm
      · intro i his
        have hn := (Finset.mem_sdiff.mp (hs' his)).2
        have hi : i ∈ r∪u := he ▸ Finset.mem_union_right r his
        exact (Finset.mem_union.mp hi).resolve_left hn
      · intro i hiu
        have hn := (Finset.mem_sdiff.mp (hu' hiu)).2
        have hi : i ∈ r∪s := he.symm ▸ Finset.mem_union_right r hiu
        exact (Finset.mem_union.mp hi).resolve_left hn
  · have hi : ¬ r ≤ t := hrt
    have hn : r ≠ t := fun he => hrt (he ▸ Finset.Subset.refl _)
    simp [Finset.Icc_eq_empty hi,hn]

lemma sum_sign_interval_in_family (D : Finset (Finset ι)) (hD : DownClosed D)
    (r t : D) :
    (∑ s : D, if r.val ⊆ s.val ∧ s.val ⊆ t.val then sign s.val else 0) =
      if r = t then sign r.val else 0 := by
  classical
  have he : (∑ s : D, if r.val ⊆ s.val ∧ s.val ⊆ t.val then sign s.val else 0) =
      ∑ s : D, if s.val ⊆ t.val then (if r.val ⊆ s.val then sign s.val else 0) else 0 := by
    apply Finset.sum_congr rfl
    intro s hs
    by_cases hr : r.val ⊆ s.val <;> by_cases ht : s.val ⊆ t.val <;> simp [hr,ht]
  rw [he,sum_subsets D hD t.val t.property (fun s => if r.val ⊆ s then sign s else 0),← Finset.sum_filter,← Finset.Icc_eq_filter_powerset,
    sum_sign_interval]
  simp only [Subtype.coe_inj]

def optimalWeights (D : Finset (Finset ι)) (ν : ι → ℝ) (s : D) : ℝ :=
  sign s.val*(∑ t : D, if s.val ⊆ t.val then 1/diagonal ν t.val else 0)/
    (mass ν s.val*denominator D ν)

lemma optimalWeights_empty (D : Finset (Finset ι)) (h0 : ∅ ∈ D)
    (ν : ι → ℝ) (hν : ∀ i, 0 < ν i ∧ ν i < 1) : optimalWeights D ν ⟨∅,h0⟩ = 1 := by
  have hG := (denominator_pos D h0 ν hν).ne'
  simp only [optimalWeights,sign,Finset.card_empty,pow_zero,Finset.empty_subset,if_true,
    one_mul,mass,Finset.prod_empty]
  exact div_self hG

lemma transform_optimalWeights (D : Finset (Finset ι)) (hD : DownClosed D)
    (h0 : ∅ ∈ D) (ν : ι → ℝ) (hν : ∀ i, 0 < ν i ∧ ν i < 1) (r : D) :
    transform D ν (optimalWeights D ν) r = sign r.val/(diagonal ν r.val*denominator D ν) := by
  classical
  let G := denominator D ν
  have hG : G ≠ 0 := (denominator_pos D h0 ν hν).ne'
  have he (s : D) : optimalWeights D ν s*mass ν s.val =
      sign s.val*(∑ t : D, if s.val ⊆ t.val then 1/diagonal ν t.val else 0)/G := by
    have hm := (mass_pos ν (fun i => (hν i).1) s.val).ne'
    dsimp [optimalWeights,G]
    field_simp
  have hs (s : D) :
      (if r.val ⊆ s.val then optimalWeights D ν s*mass ν s.val else 0) =
      ∑ t : D, (if r.val ⊆ s.val ∧ s.val ⊆ t.val then sign s.val else 0)*
        ((1/diagonal ν t.val)/G) := by
    rw [he]
    by_cases hr : r.val ⊆ s.val
    · simp only [hr,true_and,if_true,Finset.mul_sum,Finset.sum_div]
      apply Finset.sum_congr rfl
      intro t ht
      split_ifs <;> ring
    · simp [hr]
  unfold transform
  simp_rw [hs]
  rw [Finset.sum_comm]
  have ht (t : D) : (∑ s : D,
      (if r.val ⊆ s.val ∧ s.val ⊆ t.val then sign s.val else 0)*((1/diagonal ν t.val)/G)) =
      (if r = t then sign r.val else 0)*((1/diagonal ν t.val)/G) := by
    rw [← Finset.sum_mul,sum_sign_interval_in_family D hD r t]
  simp_rw [ht]
  rw [Finset.sum_eq_single r]
  · simp only [if_true]
    dsimp only [G]
    ring
  · intro t ht htr
    simp [Ne.symm htr]
  · simp

/-- Explicit weights attain the same optimum as the abstract existence theorem. -/
theorem optimalWeights_main (D : Finset (Finset ι)) (hD : DownClosed D)
    (h0 : ∅ ∈ D) (ν : ι → ℝ) (hν : ∀ i, 0 < ν i ∧ ν i < 1) :
    main D ν (optimalWeights D ν) = 1/denominator D ν := by
  have hG := (denominator_pos D h0 ν hν).ne'
  rw [main_eq_sum_squares D hD ν (fun i => (hν i).1)]
  simp_rw [transform_optimalWeights D hD h0 ν hν]
  have he (r : D) : diagonal ν r.val*(sign r.val/(diagonal ν r.val*denominator D ν))^2 =
      (1/diagonal ν r.val)/(denominator D ν)^2 := by
    have hd := (diagonal_pos ν hν r.val).ne'
    rw [div_pow,mul_pow,sign_sq]
    field_simp
  simp_rw [he]
  rw [← Finset.sum_div]
  change denominator D ν/(denominator D ν)^2 = 1/denominator D ν
  field_simp

/-- A simple but useful bound: the optimal weight at s has magnitude at most
1/nu(s), independently of the number of supports in D. -/
theorem abs_optimalWeights_le (D : Finset (Finset ι)) (h0 : ∅ ∈ D)
    (ν : ι → ℝ) (hν : ∀ i, 0 < ν i ∧ ν i < 1) (s : D) :
    |optimalWeights D ν s| ≤ 1/mass ν s.val := by
  have hm := mass_pos ν (fun i => (hν i).1) s.val
  have hG := denominator_pos D h0 ν hν
  have hs0 : 0 ≤ ∑ t : D, if s.val ⊆ t.val then 1/diagonal ν t.val else 0 := by
    apply Finset.sum_nonneg
    intro t ht
    split_ifs
    · exact (one_div_pos.mpr (diagonal_pos ν hν t.val)).le
    · exact le_rfl
  have hs : (∑ t : D, if s.val ⊆ t.val then 1/diagonal ν t.val else 0) ≤ denominator D ν := by
    apply Finset.sum_le_sum
    intro t ht
    split_ifs
    · exact le_rfl
    · exact (one_div_pos.mpr (diagonal_pos ν hν t.val)).le
  have hsign : |sign s.val| = 1 := by simp [sign]
  rw [optimalWeights,abs_div,abs_mul,hsign,one_mul,abs_of_nonneg hs0,
    abs_of_pos (mul_pos hm hG)]
  apply (div_le_iff₀ (mul_pos hm hG)).mpr
  simpa only [one_div,← mul_assoc,inv_mul_cancel₀ hm.ne',one_mul] using hs

#print axioms optimalWeights_main
#print axioms abs_optimalWeights_le
end
end Erdos952Investigation.FiniteSelbergWeights
