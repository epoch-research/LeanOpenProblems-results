import Submission.CompleteKernelBasisExplore
import Submission.PatchedGraphSetExplore
import Submission.InfiniteMixedKernelExplore

/-! One complete-partition coloring works for all later graphs, all real
kernels, and all finite or infinite coarse families. The centered matrix
norm retains the color-dimension cost; no infinite-scale construction is
asserted. -/
namespace Erdos66UniversalCompleteGraph
open Erdos66UniformColorMoments Erdos66CompleteKernelBasis
  Erdos66CompletePartitionColorTransfer Erdos66UniformGraphColorTransfer
  Erdos66TranslatedGraphPartition Erdos66GraphPatch
  Erdos66MixedDisjointAssembly Erdos66OriginRepair Erdos66DisjointPaletteAssembly
  Erdos66InfiniteKernelLocality Erdos66InfiniteMixedKernel
open scoped Classical
set_option maxHeartbeats 2800000
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {α : Type*} [Fintype α] [Nonempty α] [DecidableEq α]

noncomputable def centeredMass (K : α → α → ℝ) : ℝ :=
  ∑ q : α×α, (centeredKernel K q.1 q.2)^2

omit [Nonempty α] [DecidableEq α] in
lemma centeredMass_nonneg (K : α → α → ℝ) : 0≤centeredMass K :=
  Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)

/-- No symmetry is required of the kernel. The coloring is chosen before
both the kernel and the graph. All fine targets are controlled. -/
theorem exists_universal_graph_kernels {n : ℕ} (ρ : Fin n ≃ F) (hF : ringChar F≠2) :
    ∃ ω : Fin n → α, ∀ (f : F → F) (D : ℕ), HasBoundedSums f D →
      ∀ K : α → α → ℝ, ∀ t s : F,
        (graphSum f ρ (fun i j ↦ K (ω i) (ω j)) t s-(n:ℝ)^2*kernelMean K)^2≤
          (D:ℝ)^2*n*(8*(n:ℝ)^2+2*n)*centeredMass K := by
  obtain ⟨ω,hω⟩ := exists_universal_centered_energy (α := α) ρ hF
  refine ⟨ω,fun f D hf K t s ↦ ?_⟩
  have he := graphSum_error_sq f ρ D hf K ω t s
  have hm := mul_le_mul_of_nonneg_left (hω K) (show (0:ℝ)≤(D:ℝ)^2*n by positivity)
  exact he.trans (by simpa only [centeredMass,mul_assoc] using hm)

/-- Arbitrary finite graph patches also follow after the same kind of
universal selection. Their locations and values are not fixed beforehand. -/
theorem exists_universal_patched_kernels {n : ℕ} (ρ : Fin n ≃ F) (hF : ringChar F≠2) :
    ∃ ω : Fin n → α, ∀ (f g : F → F) (D : ℕ), HasBoundedSums f D →
      ∀ T : Finset F, (∀ x, x∉T → f x=g x) → ∀ K : α → α → ℝ, ∀ t s : F,
        (graphSum g ρ (fun i j ↦ K (ω i) (ω j)) t s-(n:ℝ)^2*kernelMean K)^2≤
          (2*(D:ℝ)^2*n+32*(T.card:ℝ)^2)*(8*(n:ℝ)^2+2*n)*centeredMass K := by
  obtain ⟨ω,hω⟩ := exists_universal_centered_energy (α := α) ρ hF
  refine ⟨ω,fun f g D hf T hfg K t s ↦ ?_⟩
  have he := patched_graph_error_sq f g D hf T hfg ρ K ω t s
  have hm := mul_le_mul_of_nonneg_left (hω K)
    (show (0:ℝ)≤2*(D:ℝ)^2*n+32*(T.card:ℝ)^2 by positivity)
  exact he.trans (by simpa only [centeredMass,mul_assoc] using hm)

variable {H : Type*} [AddCommGroup H] [DecidableEq H]

omit [Fintype α] [Nonempty α] [DecidableEq α] in
lemma graphSet_mixed_pairCount (f : F → F) {n : ℕ} (ρ : Fin n ≃ F)
    (B C : α → Finset H) (ω : Fin n → α) (t s : F) (q : H) :
    (pairCount (graphSet f ρ B ω) (graphSet f ρ C ω) ((t,s),q):ℝ)=
      graphSum f ρ (fun i j ↦ mixedKernel B C q (ω i) (ω j)) t s := by
  rw [graphSet,graphSet,assembly_mixed_pairCount _
    (fun _ _ hij ↦ graphSlice_disjoint f (fun he ↦ hij (ρ.injective he)))]
  simp_rw [graphSlice_pairCount]
  push_cast
  unfold graphSum mixedKernel
  simp only [mul_comm]

/-- The same coloring works for all later coarse families B,C, including
overlapping members, and every coarse target in an arbitrary group. -/
theorem exists_universal_actual_mixed {n : ℕ} (ρ : Fin n ≃ F) (hF : ringChar F≠2) :
    ∃ ω : Fin n → α, ∀ (f : F → F) (D : ℕ), HasBoundedSums f D →
      ∀ (B C : α → Finset H) (q : H) (t s : F),
        ((pairCount (graphSet f ρ B ω) (graphSet f ρ C ω) ((t,s),q):ℝ)-
          (n:ℝ)^2*kernelMean (mixedKernel B C q))^2≤
            (D:ℝ)^2*n*(8*(n:ℝ)^2+2*n)*centeredMass (mixedKernel B C q) := by
  obtain ⟨ω,hω⟩ := exists_universal_graph_kernels (α := α) ρ hF
  refine ⟨ω,fun f D hf B C q t s ↦ ?_⟩
  rw [graphSet_mixed_pairCount]
  exact hω f D hf (mixedKernel B C q) t s

noncomputable def infiniteGraphSet (f : F → F) {n : ℕ} (ρ : Fin n ≃ F)
    (B : α → Set ℕ) (ω : Fin n → α) : Set ((F×F)×ℤ) :=
  infiniteAssembly (fun i ↦ graphSlice f (ρ i)) (fun i ↦ B (ω i))

omit [Fintype α] [Nonempty α] [DecidableEq α] in
lemma infinite_graph_mixed_identity (f : F → F) {n : ℕ} (ρ : Fin n ≃ F)
    (B C : α → Set ℕ) (ω : Fin n → α) (q : ℕ) (t s : F) :
    (setPairCount (infiniteGraphSet f ρ B ω) (infiniteGraphSet f ρ C ω) ((t,s),(q:ℤ)):ℝ)=
      graphSum f ρ (fun i j ↦ infiniteMixedKernel B C q (ω i) (ω j)) t s := by
  unfold infiniteGraphSet
  rw [←assembly_mixed_count_locality,assembly_mixed_pairCount _
    (fun _ _ hij ↦ graphSlice_disjoint f (fun he ↦ hij (ρ.injective he)))]
  simp_rw [graphSlice_pairCount]
  push_cast
  simp only [graphSum,infiniteMixedKernel,coarse_count_locality,mul_comm]

/-- This is a genuine infinite-coarse-set theorem, not a finite-support
convention. The coloring precedes B,C and all their natural targets. The
ambient remains a finite field plane times nonnegative integer coordinates. -/
theorem exists_universal_infinite_mixed {n : ℕ} (ρ : Fin n ≃ F) (hF : ringChar F≠2) :
    ∃ ω : Fin n → α, ∀ (f : F → F) (D : ℕ), HasBoundedSums f D →
      ∀ (B C : α → Set ℕ) (q : ℕ) (t s : F),
        ((setPairCount (infiniteGraphSet f ρ B ω) (infiniteGraphSet f ρ C ω) ((t,s),(q:ℤ)):ℝ)-
          (n:ℝ)^2*kernelMean (infiniteMixedKernel B C q))^2≤
            (D:ℝ)^2*n*(8*(n:ℝ)^2+2*n)*centeredMass (infiniteMixedKernel B C q) := by
  obtain ⟨ω,hω⟩ := exists_universal_graph_kernels (α := α) ρ hF
  refine ⟨ω,fun f D hf B C q t s ↦ ?_⟩
  rw [infinite_graph_mixed_identity]
  exact hω f D hf (infiniteMixedKernel B C q) t s

/-- The infinite-coarse version also permits arbitrary later graph patches.
No finite list of coarse targets or patch-dependent re-selection occurs. -/
theorem exists_universal_infinite_patched {n : ℕ} (ρ : Fin n ≃ F) (hF : ringChar F≠2) :
    ∃ ω : Fin n → α, ∀ (f g : F → F) (D : ℕ), HasBoundedSums f D →
      ∀ T : Finset F, (∀ x, x∉T → f x=g x) →
      ∀ (B C : α → Set ℕ) (q : ℕ) (t s : F),
        ((setPairCount (infiniteGraphSet g ρ B ω) (infiniteGraphSet g ρ C ω) ((t,s),(q:ℤ)):ℝ)-
          (n:ℝ)^2*kernelMean (infiniteMixedKernel B C q))^2≤
            (2*(D:ℝ)^2*n+32*(T.card:ℝ)^2)*(8*(n:ℝ)^2+2*n)*
              centeredMass (infiniteMixedKernel B C q) := by
  obtain ⟨ω,hω⟩ := exists_universal_patched_kernels (α := α) ρ hF
  refine ⟨ω,fun f g D hf T hfg B C q t s ↦ ?_⟩
  rw [infinite_graph_mixed_identity]
  exact hω f g D hf T hfg (infiniteMixedKernel B C q) t s

/-- Exact prefix agreement is retained for a FIXED graph and coloring.
This is not compatibility between different fine moduli. -/
lemma infinite_graph_prefix_congr (f : F → F) {n : ℕ} (ρ : Fin n ≃ F)
    (ω : Fin n → α) (B C B' C' : α → Set ℕ) {N q : ℕ} (hq : q≤N)
    (hB : ∀ a k, k≤N → (k∈B a ↔ k∈B' a))
    (hC : ∀ a k, k≤N → (k∈C a ↔ k∈C' a)) (z : F×F) :
    setPairCount (infiniteGraphSet f ρ B ω) (infiniteGraphSet f ρ C ω) (z,(q:ℤ))=
      setPairCount (infiniteGraphSet f ρ B' ω) (infiniteGraphSet f ρ C' ω) (z,(q:ℤ)) :=
  mixed_count_prefix_congr (fun i ↦ graphSlice f (ρ i))
    (fun i ↦ B (ω i)) (fun i ↦ C (ω i)) (fun i ↦ B' (ω i)) (fun i ↦ C' (ω i))
    hq (fun i ↦ hB (ω i)) (fun i ↦ hC (ω i)) z

end Erdos66UniversalCompleteGraph
