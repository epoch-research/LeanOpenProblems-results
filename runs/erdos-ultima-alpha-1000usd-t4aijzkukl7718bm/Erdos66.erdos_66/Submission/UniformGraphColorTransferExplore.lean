import Submission.TranslatedGraphPartitionExplore

/-! One color assignment is selected before every later bounded-sum graph.
This is a finite-group transfer, not a compatible integer construction. -/
namespace Erdos66UniformGraphColorTransfer
open Erdos66UniformSelection Erdos66UniformColorMoments Erdos66FixedPatternColorEnergy
  Erdos66CompletePartitionColorTransfer Erdos66TranslatedGraphPartition
  Erdos66OriginRepair Erdos66DisjointPaletteAssembly Erdos66ActualColorRootTransfer
open scoped Classical
set_option maxHeartbeats 2600000

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {α : Type*} [Fintype α] [Nonempty α] [DecidableEq α]

lemma graphSum_centered (f : F → F) {n : ℕ} (ρ : Fin n ≃ F) (K : α → α → ℝ)
    (ω : Fin n → α) (t s : F) :
    graphSum f ρ (fun i j ↦ centeredKernel K (ω i) (ω j)) t s=
      graphSum f ρ (fun i j ↦ K (ω i) (ω j)) t s-(n:ℝ)^2*kernelMean K := by
  have he : graphSum f ρ (fun i j ↦ centeredKernel K (ω i) (ω j)) t s=
      graphSum f ρ (fun i j ↦ K (ω i) (ω j)) t s-kernelMean K*graphSum f ρ (fun _ _ ↦ 1) t s := by
    simp only [graphSum,centeredKernel,sub_mul,Finset.sum_sub_distrib,Finset.mul_sum,one_mul]
  rw [he,graphSum_one]
  ring

lemma graphSum_error_sq (f : F → F) {n : ℕ} (ρ : Fin n ≃ F) (D : ℕ) (hf : HasBoundedSums f D)
    (K : α → α → ℝ) (ω : Fin n → α) (t s : F) :
    (graphSum f ρ (fun i j ↦ K (ω i) (ω j)) t s-(n:ℝ)^2*kernelMean K)^2≤
      (D:ℝ)^2*(n:ℝ)*Erdos66CompletePartitionColorTransfer.colorEnergy ρ K ω := by
  rw [←graphSum_centered]
  exact graphSum_sq_le_energy f ρ D hf _ t s

lemma exists_energy_budget {ι : Type*} {n : ℕ} (ρ : Fin n ≃ F) (hF : ringChar F≠2)
    (S : Finset ι) (K : ι → α → α → ℝ) (hK : ∀ k∈S, ∀ x y, K k x y=K k y x)
    (w : ι → ℝ) (hw : ∀ k∈S, 0≤w k) :
    ∃ ω : Fin n → α, ∀ k∈S,
      w k*Erdos66CompletePartitionColorTransfer.colorEnergy ρ (K k) ω≤kernelBudget n S K w := by
  obtain ⟨ω,hω⟩ := exists_le_mean (fun ω : Fin n → α ↦
    ∑ k∈S, w k*Erdos66CompletePartitionColorTransfer.colorEnergy ρ (K k) ω)
  have hbudget : (∑ k∈S, w k*Erdos66CompletePartitionColorTransfer.colorEnergy ρ (K k) ω) ≤
      kernelBudget n S K w := by
    apply hω.trans
    rw [mean_sum]
    apply Finset.sum_le_sum
    intro k hk
    rw [mean_const_mul]
    exact mul_le_mul_of_nonneg_left
      (Erdos66CompletePartitionColorTransfer.mean_colorEnergy_le ρ hF (K k) (hK k hk)) (hw k hk)
  refine ⟨ω,fun k hk ↦ ?_⟩
  exact (Finset.single_le_sum (fun j hj ↦ mul_nonneg (hw j hj)
    (Erdos66CompletePartitionColorTransfer.colorEnergy_nonneg ρ (K j) ω)) hk).trans hbudget

/-- Both the graph and its bound may be chosen AFTER the coloring. No
number-of-graphs or number-of-fine-targets factor occurs. -/
theorem exists_uniform_graph_budget {ι : Type*} {n : ℕ} (ρ : Fin n ≃ F) (hF : ringChar F≠2)
    (S : Finset ι) (K : ι → α → α → ℝ) (hK : ∀ k∈S, ∀ x y, K k x y=K k y x)
    (w : ι → ℝ) (hw : ∀ k∈S, 0≤w k) :
    ∃ ω : Fin n → α, ∀ (f : F → F) (D : ℕ), HasBoundedSums f D →
      ∀ k∈S, ∀ t s : F,
        w k*(graphSum f ρ (fun i j ↦ K k (ω i) (ω j)) t s-(n:ℝ)^2*kernelMean (K k))^2≤
          (D:ℝ)^2*(n:ℝ)*kernelBudget n S K w := by
  obtain ⟨ω,hω⟩ := exists_energy_budget ρ hF S K hK w hw
  refine ⟨ω,fun f D hf k hk t s ↦ ?_⟩
  have he := mul_le_mul_of_nonneg_left (graphSum_error_sq f ρ D hf (K k) ω t s) (hw k hk)
  have he' := mul_le_mul_of_nonneg_left (hω k hk) (show (0:ℝ)≤(D:ℝ)^2*n by positivity)
  nlinarith only [he,he']

variable {H : Type*} [AddCommGroup H] [DecidableEq H]

noncomputable def graphSet (f : F → F) {n : ℕ} (ρ : Fin n ≃ F)
    (B : α → Finset H) (ω : Fin n → α) : Finset ((F×F)×H) :=
  assembly (fun i ↦ graphSlice f (ρ i)) (fun i ↦ B (ω i))

lemma mem_graphSet (f : F → F) {n : ℕ} (ρ : Fin n ≃ F)
    (B : α → Finset H) (ω : Fin n → α) (z : F×F) (q : H) :
    (z,q)∈graphSet f ρ B ω ↔ q∈B (ω (ρ.symm (z.2-f z.1))) := by
  simp only [graphSet,assembly,Finset.mem_biUnion,Finset.mem_univ,true_and,Finset.mem_product,mem_graphSlice]
  constructor
  · rintro ⟨i,hi,hq⟩
    have he : ρ.symm (z.2-f z.1)=i := by
      apply ρ.injective
      rw [ρ.apply_symm_apply,hi]
      ring
    rwa [he]
  · intro hq
    refine ⟨ρ.symm (z.2-f z.1),?_,hq⟩
    rw [ρ.apply_symm_apply]
    ring

lemma graphSet_pairCount (f : F → F) {n : ℕ} (ρ : Fin n ≃ F)
    (B : α → Finset H) (ω : Fin n → α) (t s : F) (q : H) :
    (pairCount (graphSet f ρ B ω) (graphSet f ρ B ω) ((t,s),q):ℝ)=
      graphSum f ρ (fun i j ↦ coarseKernel B q (ω i) (ω j)) t s := by
  rw [graphSet,assembly_pairCount _
    (fun _ _ hij ↦ graphSlice_disjoint f (fun he ↦ hij (ρ.injective he)))]
  simp_rw [graphSlice_pairCount]
  push_cast
  unfold graphSum coarseKernel
  simp only [mul_comm]

/-- The actual-set version, retaining the same coloring for every later
graph with bounded sum fibers. Coarse color sets may overlap arbitrarily. -/
theorem exists_actual_uniform_graph_budget {n : ℕ} (ρ : Fin n ≃ F) (hF : ringChar F≠2)
    (B : α → Finset H) (S : Finset H) (w : H → ℝ) (hw : ∀ q∈S, 0≤w q) :
    ∃ ω : Fin n → α, ∀ (f : F → F) (D : ℕ), HasBoundedSums f D →
      ∀ q∈S, ∀ t s : F,
        w q*((pairCount (graphSet f ρ B ω) (graphSet f ρ B ω) ((t,s),q):ℝ)-
          (n:ℝ)^2*kernelMean (coarseKernel B q))^2≤
        (D:ℝ)^2*(n:ℝ)*kernelBudget n S (coarseKernel B) w := by
  obtain ⟨ω,hω⟩ := exists_uniform_graph_budget ρ hF S (coarseKernel B)
    (fun q hq ↦ coarseKernel_symm B q) w hw
  refine ⟨ω,fun f D hf q hq t s ↦ ?_⟩
  rw [graphSet_pairCount]
  exact hω f D hf q hq t s

end Erdos66UniformGraphColorTransfer
