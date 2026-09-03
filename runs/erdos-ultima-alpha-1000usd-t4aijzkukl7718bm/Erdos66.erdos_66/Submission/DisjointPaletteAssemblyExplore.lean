import Submission.SharedParameterSetExplore

/-! Exact set assemblies for disjoint fine palettes, and a weighted transfer
from entrywise L1 errors of their mixed-count matrices. -/
namespace Erdos66DisjointPaletteAssembly
open Erdos66OriginRepair Erdos66ParabolaRepair Erdos66CommonOriginFamily
  Erdos66SharedParameterSet Erdos66CyclicVariance
open scoped Classical
set_option maxHeartbeats 2200000

variable {G H ι : Type*} [AddCommGroup G] [DecidableEq G]
  [AddCommGroup H] [DecidableEq H] [Fintype ι] [DecidableEq ι]

lemma pairCount_biUnion_left (S : Finset ι) (A : ι → Finset G)
    (hA : (S:Set ι).PairwiseDisjoint A) (B : Finset G) (z : G) :
    pairCount (S.biUnion A) B z=∑ i∈S, pairCount (A i) B z := by
  unfold pairCount
  rw [Finset.filter_biUnion]
  apply Finset.card_biUnion
  intro i hi j hj hij
  exact (hA hi hj hij).mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)

lemma pairCount_biUnion_right (S : Finset ι) (A : ι → Finset G)
    (hA : (S:Set ι).PairwiseDisjoint A) (B : Finset G) (z : G) :
    pairCount B (S.biUnion A) z=∑ i∈S, pairCount B (A i) z := by
  rw [pairCount_comm,pairCount_biUnion_left S A hA]
  simp_rw [pairCount_comm (A _)]

lemma pairCount_biUnion_self (S : Finset ι) (A : ι → Finset G)
    (hA : (S:Set ι).PairwiseDisjoint A) (z : G) :
    pairCount (S.biUnion A) (S.biUnion A) z=∑ i∈S, ∑ j∈S, pairCount (A i) (A j) z := by
  rw [pairCount_biUnion_left S A hA]
  simp_rw [pairCount_biUnion_right S A hA]

noncomputable def assembly (P : ι → Finset G) (B : ι → Finset H) : Finset (G×H) :=
  Finset.univ.biUnion (fun i ↦ P i ×ˢ B i)

lemma assembly_pairwise (P : ι → Finset G) (hP : Pairwise (fun i j ↦ Disjoint (P i) (P j)))
    (B : ι → Finset H) :
    ((Finset.univ:Finset ι):Set ι).PairwiseDisjoint (fun i ↦ P i ×ˢ B i) := by
  intro i hi j hj hij
  apply Finset.disjoint_left.mpr
  intro z hz hz'
  exact Finset.disjoint_left.mp (hP hij) (Finset.mem_product.mp hz).1 (Finset.mem_product.mp hz').1

/-- The coarse sets may overlap arbitrarily. Disjointness is required only
of the fine palette, so each assembled point has a unique label. -/
theorem assembly_pairCount (P : ι → Finset G) (hP : Pairwise (fun i j ↦ Disjoint (P i) (P j)))
    (B : ι → Finset H) (z : G) (q : H) :
    pairCount (assembly P B) (assembly P B) (z,q)=
      ∑ i : ι, ∑ j : ι, pairCount (P i) (P j) z*pairCount (B i) (B j) q := by
  rw [assembly,pairCount_biUnion_self _ _ (assembly_pairwise P hP B)]
  simp_rw [pairCount_product]

lemma weighted_matrix_error (P C : ι → Finset G) (K : ι → ι → ℝ)
    (M E : ℝ) (hM : 0≤M) (hK : ∀ i j, |K i j|≤M) (z : G)
    (hE : (∑ i : ι, ∑ j : ι, |(pairCount (P i) (P j) z:ℝ)-pairCount (C i) (C j) z|)≤E) :
    |(∑ i : ι, ∑ j : ι, K i j*(pairCount (P i) (P j) z:ℝ))-
      (∑ i : ι, ∑ j : ι, K i j*(pairCount (C i) (C j) z:ℝ))| ≤ M*E := by
  simp_rw [←Finset.sum_sub_distrib,←mul_sub]
  calc
    _ ≤ ∑ i : ι, ∑ j : ι,
        |K i j*((pairCount (P i) (P j) z:ℝ)-pairCount (C i) (C j) z)| :=
      (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun _ _ ↦ Finset.abs_sum_le_sum_abs _ _))
    _ ≤ ∑ i : ι, ∑ j : ι,
        M*|(pairCount (P i) (P j) z:ℝ)-pairCount (C i) (C j) z| := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (hK i j) (abs_nonneg _)
    _ = M*(∑ i : ι, ∑ j : ι, |(pairCount (P i) (P j) z:ℝ)-pairCount (C i) (C j) z|) := by
      simp only [Finset.mul_sum]
    _ ≤ M*E := mul_le_mul_of_nonneg_left hE hM

/-- A matrix-level L1 estimate transfers to an actual set with arbitrary
coarse colors. No disjointness of the coarse colors is assumed. -/
theorem assembly_error (P C : ι → Finset G)
    (hP : Pairwise (fun i j ↦ Disjoint (P i) (P j))) (B : ι → Finset H)
    (M E : ℝ) (hM : 0≤M) (z : G) (q : H)
    (hB : ∀ i j, (pairCount (B i) (B j) q:ℝ)≤M)
    (hE : (∑ i : ι, ∑ j : ι, |(pairCount (P i) (P j) z:ℝ)-pairCount (C i) (C j) z|)≤E) :
    |(pairCount (assembly P B) (assembly P B) (z,q):ℝ)-
      (∑ i : ι, ∑ j : ι, (pairCount (B i) (B j) q:ℝ)*(pairCount (C i) (C j) z:ℝ))| ≤ M*E := by
  rw [assembly_pairCount P hP B z q]
  push_cast
  have he := weighted_matrix_error P C (fun i j ↦ (pairCount (B i) (B j) q:ℝ)) M E hM
    (fun i j ↦ by rw [abs_of_nonneg (Nat.cast_nonneg _)]; exact hB i j) z hE
  simpa only [mul_comm] using he

end Erdos66DisjointPaletteAssembly
