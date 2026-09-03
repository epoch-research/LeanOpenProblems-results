import Submission.NestedDifferencePaletteExplore
import Submission.InfiniteMixedKernelExplore

/-! Universal mixed transfer with a cyclic fine coordinate. The output is
still in ZMod M x Nat; integer radix carry control is a separate step. -/
namespace Erdos66UniversalCyclicCoarse
open Erdos66OriginRepair Erdos66DisjointPaletteAssembly
  Erdos66MixedDisjointAssembly Erdos66InfiniteKernelLocality
  Erdos66InfiniteMixedKernel Erdos66NestedDifferencePalette Erdos66OuterCarryProfile
open scoped Classical
set_option maxHeartbeats 2400000

variable {G ι : Type*} [AddCommGroup G] [DecidableEq G]
  [Fintype ι] [DecidableEq ι]

lemma nonnegative_weighted_pair_error (P : ι → Finset G) (z : G) (μ E : ℝ)
    (hP : ∀ i j, |(pairCount (P i) (P j) z:ℝ)-μ| ≤ E)
    (W : ι → ι → ℝ) (hW : ∀ i j, 0 ≤ W i j) :
    |(∑ i : ι, ∑ j : ι, (pairCount (P i) (P j) z:ℝ)*W i j)-
        μ*(∑ i : ι, ∑ j : ι, W i j)| ≤
      E*(∑ i : ι, ∑ j : ι, W i j) := by
  simp_rw [Finset.mul_sum,←Finset.sum_sub_distrib,←sub_mul]
  calc
    _ ≤ ∑ i : ι, ∑ j : ι, |((pairCount (P i) (P j) z:ℝ)-μ)*W i j| :=
      (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum (fun i hi ↦ Finset.abs_sum_le_sum_abs _ _))
    _ ≤ ∑ i : ι, ∑ j : ι, E*W i j := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      rw [abs_mul,abs_of_nonneg (hW i j)]
      exact mul_le_mul_of_nonneg_right (hP i j) (hW i j)

lemma infinite_mixed_count_identity (P : ι → Finset G)
    (hP : Pairwise (fun i j ↦ Disjoint (P i) (P j)))
    (B C : ι → Set ℕ) (n : ℕ) (z : G) :
    (setPairCount (infiniteAssembly P B) (infiniteAssembly P C) (z,(n:ℤ)):ℝ) =
      ∑ i : ι, ∑ j : ι, (pairCount (P i) (P j) z:ℝ)*infiniteMixedKernel B C n i j := by
  rw [←assembly_mixed_count_locality,assembly_mixed_pairCount P hP]
  simp only [Nat.cast_sum,Nat.cast_mul,coarse_count_locality,infiniteMixedKernel]

lemma infinite_mixed_count_error (P : ι → Finset G)
    (hP : Pairwise (fun i j ↦ Disjoint (P i) (P j)))
    (μ E : ℝ) (hflat : ∀ i j z, |(pairCount (P i) (P j) z:ℝ)-μ| ≤ E)
    (B C : ι → Set ℕ) (n : ℕ) (z : G) :
    |(setPairCount (infiniteAssembly P B) (infiniteAssembly P C) (z,(n:ℤ)):ℝ)-
        μ*(∑ i : ι, ∑ j : ι, infiniteMixedKernel B C n i j)| ≤
      E*(∑ i : ι, ∑ j : ι, infiniteMixedKernel B C n i j) := by
  rw [infinite_mixed_count_identity P hP]
  exact nonnegative_weighted_pair_error P z μ E (fun i j ↦ hflat i j z)
    (infiniteMixedKernel B C n) (infiniteMixedKernel_nonneg B C n)

/-- Disjoint cyclic colors are chosen before all later infinite coarse
families. Their common entrywise mean is logarithmically tuned. -/
theorem exists_universal_cyclic_infinite_transfer (c τ δ : ℝ)
    (hc : 0<c) (hτ : 0<τ) (hδ : 0<δ) (q N₀ : ℕ) :
    ∃ M : ℕ, N₀<M ∧ Odd M ∧ ∃ hM : NeZero M,
      ∃ μ : ℝ, 0<μ ∧ |μ/Real.log M-c|<τ ∧
        ∃ P : Fin q → Finset (ZMod M),
          Pairwise (fun i j ↦ Disjoint (P i) (P j)) ∧
          ∀ (B C : Fin q → Set ℕ) (n : ℕ) (z : ZMod M),
            |(setPairCount (infiniteAssembly P B) (infiniteAssembly P C) (z,(n:ℤ)):ℝ)-
                μ*(∑ i : Fin q, ∑ j : Fin q, infiniteMixedKernel B C n i j)| ≤
              δ*μ*(∑ i : Fin q, ∑ j : Fin q, infiniteMixedKernel B C n i j) := by
  obtain ⟨M,hMN,hodd,hM,μ,hμ,htune,P,hP,hflat⟩ :=
    exists_logarithmic_disjoint_cyclic_palette c τ δ hc hτ hδ q N₀
  letI := hM
  refine ⟨M,hMN,hodd,hM,μ,hμ,htune,P,hP,fun B C n z ↦ ?_⟩
  exact infinite_mixed_count_error P hP μ (δ*μ) hflat B C n z

end Erdos66UniversalCyclicCoarse
