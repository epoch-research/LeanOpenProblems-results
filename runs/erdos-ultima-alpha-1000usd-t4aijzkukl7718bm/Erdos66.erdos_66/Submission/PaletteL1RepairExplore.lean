import Submission.OrientedEdgeRepairExplore

/-! Matrix L1 control from a common erased palette and total repair budgets. -/
namespace Erdos66PaletteL1Repair
open Erdos66OriginRepair Erdos66ParabolaRepair Erdos66AsymmetricRepair
  Erdos66DisjointPaletteAssembly Erdos66CommonOriginFamily Erdos66CyclicVariance
open scoped Classical
set_option maxHeartbeats 2400000

lemma matrix_L1_le_common_lower {ι : Type*} [Fintype ι]
    (A B L : ι → ι → ℝ) (a b : ℝ) (hLA : ∀ i j, L i j≤A i j) (hLB : ∀ i j, L i j≤B i j)
    (hA : (∑ i : ι, ∑ j : ι, A i j) ≤ (∑ i : ι, ∑ j : ι, L i j)+a)
    (hB : (∑ i : ι, ∑ j : ι, B i j) ≤ (∑ i : ι, ∑ j : ι, L i j)+b) :
    (∑ i : ι, ∑ j : ι, |A i j-B i j|)≤a+b := by
  have he : (∑ i : ι, ∑ j : ι, |A i j-B i j|)≤
      ∑ i : ι, ∑ j : ι, ((A i j-L i j)+(B i j-L i j)) := by
    apply Finset.sum_le_sum
    intro i hi
    apply Finset.sum_le_sum
    intro j hj
    apply abs_le.mpr
    constructor <;> linarith [hLA i j,hLB i j]
  simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib] at he
  linarith

variable {G ι : Type*} [AddCommGroup G] [DecidableEq G] [Fintype ι] [DecidableEq ι]

lemma pairCount_singleton_left (A : Finset G) (z : G) :
    pairCount {0} A z=if z∈A then 1 else 0 := by
  by_cases hz : z∈A <;> simp [pairCount,Finset.filter_singleton,hz]

lemma pairCount_singleton_right (A : Finset G) (z : G) :
    pairCount A {0} z=if z∈A then 1 else 0 := by rw [pairCount_comm,pairCount_singleton_left]

lemma pairCount_add_zero (A B : Finset G) (hA : (0:G)∉A) (hB : (0:G)∉B) (z : G) :
    pairCount (A∪{0}) (B∪{0}) z=pairCount A B z+
      (if z∈A then 1 else 0)+(if z∈B then 1 else 0)+(if z=0 then 1 else 0) := by
  rw [pairCount_union_mixed _ _ _ _ _ (by simpa using hA) (by simpa using hB),
    pairCount_singleton_right,pairCount_singleton_left,pairCount_singleton_left]
  simp only [Finset.mem_singleton]

lemma sum_membership_disjoint (E : ι → Finset G)
    (hE : Pairwise (fun i j ↦ Disjoint (E i) (E j))) (z : G) :
    (∑ i : ι, if z∈E i then (1:ℝ) else 0)=
      if z∈Finset.univ.biUnion E then 1 else 0 := by
  have he := pairCount_biUnion_left Finset.univ E (fun _ _ _ _ hij ↦ hE hij) ({0}:Finset G) z
  simp_rw [pairCount_singleton_right] at he
  exact_mod_cast he.symm

lemma reference_sum_erase_bound (C E : ι → Finset G)
    (hE : Pairwise (fun i j ↦ Disjoint (E i) (E j)))
    (hE0 : ∀ i, (0:G)∉E i) (hC : ∀ i, C i=E i∪{0}) (z : G) (hz : z≠0) :
    (∑ i : ι, ∑ j : ι, (pairCount (C i) (C j) z:ℝ)) ≤
      (∑ i : ι, ∑ j : ι, (pairCount (E i) (E j) z:ℝ))+2*Fintype.card ι := by
  have he (i j : ι) : (pairCount (C i) (C j) z:ℝ)=
      (pairCount (E i) (E j) z:ℝ)+(if z∈E i then 1 else 0)+(if z∈E j then 1 else 0) := by
    rw [hC i,hC j,pairCount_add_zero _ _ (hE0 i) (hE0 j)]
    simp only [hz,if_false,add_zero,Nat.cast_add,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
  simp_rw [he]
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  rw [←Finset.mul_sum,sum_membership_disjoint E hE]
  split_ifs <;> simp only [mul_zero,mul_one] <;> nlinarith [(Nat.cast_nonneg (Fintype.card ι): (0:ℝ)≤_)]

/-- A disjoint repaired palette has matrix L1 error bounded by its total
repair cost and the total lost-origin cost. -/
theorem palette_L1_nonzero (C E P : ι → Finset G)
    (hE : Pairwise (fun i j ↦ Disjoint (E i) (E j))) (hE0 : ∀ i, (0:G)∉E i)
    (hC : ∀ i, C i=E i∪{0}) (hEP : ∀ i, E i⊆P i)
    (R : ℝ) (z : G) (hz : z≠0)
    (hR : (∑ i : ι, ∑ j : ι, (pairCount (P i) (P j) z:ℝ)) ≤
      (∑ i : ι, ∑ j : ι, (pairCount (E i) (E j) z:ℝ))+R) :
    (∑ i : ι, ∑ j : ι, |(pairCount (P i) (P j) z:ℝ)-pairCount (C i) (C j) z|)≤
      R+2*Fintype.card ι := by
  apply matrix_L1_le_common_lower _ _
    (fun i j ↦ (pairCount (E i) (E j) z:ℝ)) R (2*Fintype.card ι)
  · intro i j
    exact_mod_cast pairCount_mono (hEP i) (hEP j) z
  · intro i j
    have hi : E i⊆C i := by rw [hC i]; exact Finset.subset_union_left
    have hj : E j⊆C j := by rw [hC j]; exact Finset.subset_union_left
    exact_mod_cast pairCount_mono hi hj z
  · exact hR
  · exact reference_sum_erase_bound C E hE hE0 hC z hz

lemma palette_L1_origin (C P : ι → Finset G)
    (hC : ∀ i j, pairCount (C i) (C j) 0=1)
    (hP : ∀ i j, pairCount (P i) (P j) 0=if i=j then 0 else 1) :
    (∑ i : ι, ∑ j : ι, |(pairCount (P i) (P j) 0:ℝ)-pairCount (C i) (C j) 0|)=Fintype.card ι := by
  simp only [hC,hP,Nat.cast_ite,Nat.cast_zero,Nat.cast_one]
  have he (i j : ι) : |(if i=j then (0:ℝ) else 1)-1|=if j=i then 1 else 0 := by
    by_cases hij : i=j
    · subst j; norm_num
    · simp [hij,Ne.symm hij]
  simp_rw [he]
  simp

end Erdos66PaletteL1Repair
