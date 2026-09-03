import Submission.ParallelParabolaPartitionExplore
import Submission.ActualColorRootTransferExplore

/-! Color selection over a complete partition. There is no sparse fixed
support and no old-pattern energy or origin-multiplicity correction. -/
namespace Erdos66CompletePartitionColorTransfer
open Erdos66UniformSelection Erdos66UniformColorMoments Erdos66FixedPatternColorEnergy
  Erdos66CenteredColorSelection Erdos66FiberColorEnergy Erdos66ParallelParabolaPartition
  Erdos66OriginRepair Erdos66DisjointPaletteAssembly Erdos66ActualColorRootTransfer
open scoped Classical
set_option maxHeartbeats 2600000

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {α : Type*} [Fintype α] [Nonempty α] [DecidableEq α]

noncomputable def colorEnergy {n : ℕ} (ρ : Fin n ≃ F) (K : α → α → ℝ) (ω : Fin n → α) : ℝ :=
  energy n (fun i j ↦ ρ i+ρ j) (fun i j ↦ centeredKernel K (ω i) (ω j))

lemma colorEnergy_nonneg {n : ℕ} (ρ : Fin n ≃ F) (K : α → α → ℝ) (ω : Fin n → α) :
    0≤colorEnergy ρ K ω := by
  unfold colorEnergy energy
  exact Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)

lemma mean_colorEnergy_le {n : ℕ} (ρ : Fin n ≃ F) (hF : ringChar F≠2)
    (K : α → α → ℝ) (hK : ∀ x y, K x y=K y x) :
    mean (colorEnergy ρ K) ≤ 8*(n:ℝ)^2*colorVariance K+2*(n:ℝ)*diagonalCenteredSecond K :=
  mean_centered_energy_le (fun i j ↦ ρ i+ρ j) (labelSum_symm ρ) (labelSum_cancel ρ)
    (labelSum_diag_injective ρ hF) K hK

lemma rootSum_centered {n : ℕ} (ρ : Fin n ≃ F) (K : α → α → ℝ)
    (ω : Fin n → α) (t s : F) :
    rootSum ρ (fun i j ↦ centeredKernel K (ω i) (ω j)) t s=
      rootSum ρ (fun i j ↦ K (ω i) (ω j)) t s-(n:ℝ)^2*kernelMean K := by
  have he : rootSum ρ (fun i j ↦ centeredKernel K (ω i) (ω j)) t s=
      rootSum ρ (fun i j ↦ K (ω i) (ω j)) t s-kernelMean K*rootSum ρ (fun _ _ ↦ 1) t s := by
    simp only [rootSum,centeredKernel,sub_mul,Finset.sum_sub_distrib,Finset.mul_sum,one_mul]
  rw [he,rootSum_one]
  ring

/-- No residual sign-pattern term remains: constant kernels give exactly
constant fine-target counts. -/
lemma rootSum_error_sq {n : ℕ} (ρ : Fin n ≃ F) (hF : ringChar F≠2)
    (K : α → α → ℝ) (ω : Fin n → α) (t s : F) :
    (rootSum ρ (fun i j ↦ K (ω i) (ω j)) t s-(n:ℝ)^2*kernelMean K)^2≤
      4*(n:ℝ)*colorEnergy ρ K ω := by
  rw [←rootSum_centered]
  exact rootSum_sq_le_energy ρ hF _ t s

noncomputable def kernelBudget {ι : Type*} (n : ℕ) (S : Finset ι)
    (K : ι → α → α → ℝ) (w : ι → ℝ) : ℝ :=
  ∑ k∈S, w k*(8*(n:ℝ)^2*colorVariance (K k)+2*(n:ℝ)*diagonalCenteredSecond (K k))

/-- One coloring controls a finite family and every fine target. The
partition and its label equivalence are fixed before all kernel data. -/
theorem exists_root_budget {ι : Type*} {n : ℕ} (ρ : Fin n ≃ F) (hF : ringChar F≠2)
    (S : Finset ι) (K : ι → α → α → ℝ) (hK : ∀ k∈S, ∀ x y, K k x y=K k y x)
    (w : ι → ℝ) (hw : ∀ k∈S, 0≤w k) :
    ∃ ω : Fin n → α, ∀ k∈S, ∀ t s : F,
      w k*(rootSum ρ (fun i j ↦ K k (ω i) (ω j)) t s-(n:ℝ)^2*kernelMean (K k))^2≤
        4*(n:ℝ)*kernelBudget n S K w := by
  obtain ⟨ω,hω⟩ := exists_le_mean (fun ω : Fin n → α ↦ ∑ k∈S, w k*colorEnergy ρ (K k) ω)
  have hbudget : (∑ k∈S, w k*colorEnergy ρ (K k) ω) ≤ kernelBudget n S K w := by
    apply hω.trans
    rw [mean_sum]
    apply Finset.sum_le_sum
    intro k hk
    rw [mean_const_mul]
    exact mul_le_mul_of_nonneg_left (mean_colorEnergy_le ρ hF (K k) (hK k hk)) (hw k hk)
  refine ⟨ω,fun k hk t s ↦ ?_⟩
  have hkE : w k*colorEnergy ρ (K k) ω≤kernelBudget n S K w :=
    (Finset.single_le_sum (fun j hj ↦ mul_nonneg (hw j hj) (colorEnergy_nonneg ρ (K j) ω)) hk).trans hbudget
  have he := mul_le_mul_of_nonneg_left (rootSum_error_sq ρ hF (K k) ω t s) (hw k hk)
  have he' := mul_le_mul_of_nonneg_left hkE (show (0:ℝ)≤4*n by positivity)
  nlinarith only [he,he']

variable {H : Type*} [AddCommGroup H] [DecidableEq H]

noncomputable def coloredSet {n : ℕ} (ρ : Fin n ≃ F) (B : α → Finset H) (ω : Fin n → α) :
    Finset ((F×F)×H) := assembly (fun i ↦ parallelCurve (ρ i)) (fun i ↦ B (ω i))

/-- Every fine point has exactly one coarse color slice. Unlike a sparse
palette, no fine point is excluded independently of the coarse data. -/
lemma mem_coloredSet {n : ℕ} (ρ : Fin n ≃ F) (B : α → Finset H) (ω : Fin n → α)
    (z : F×F) (q : H) :
    (z,q)∈coloredSet ρ B ω ↔ q∈B (ω (ρ.symm (z.2-z.1^2))) := by
  simp only [coloredSet,assembly,Finset.mem_biUnion,Finset.mem_univ,true_and,Finset.mem_product,
    mem_parallelCurve]
  constructor
  · rintro ⟨i,hi,hq⟩
    have he : ρ.symm (z.2-z.1^2)=i := by
      apply ρ.injective
      rw [ρ.apply_symm_apply,hi]
      ring
    rwa [he]
  · intro hq
    refine ⟨ρ.symm (z.2-z.1^2),?_,hq⟩
    rw [ρ.apply_symm_apply]
    ring

lemma coloredSet_card {n : ℕ} (ρ : Fin n ≃ F) (B : α → Finset H) (ω : Fin n → α) :
    (coloredSet ρ B ω).card=n*(∑ i : Fin n, (B (ω i)).card) := by
  unfold coloredSet assembly
  rw [Finset.card_biUnion (assembly_pairwise (fun i ↦ parallelCurve (ρ i))
    (fun _ _ hij ↦ parallelCurve_disjoint (fun he ↦ hij (ρ.injective he))) (fun i ↦ B (ω i)))]
  simp only [Finset.card_product,parallelCurve_card]
  have hcard : Fintype.card F=n := by simpa only [Fintype.card_fin] using (Fintype.card_congr ρ).symm
  rw [hcard,Finset.mul_sum]

lemma coloredSet_fine_projection {n : ℕ} (ρ : Fin n ≃ F) (B : α → Finset H)
    (hB : ∀ x, (B x).Nonempty) (ω : Fin n → α) :
    (coloredSet ρ B ω).image Prod.fst=Finset.univ := by
  ext z
  simp only [Finset.mem_univ,iff_true,Finset.mem_image]
  obtain ⟨q,hq⟩ := hB (ω (ρ.symm (z.2-z.1^2)))
  exact ⟨(z,q),(mem_coloredSet ρ B ω z q).mpr hq,rfl⟩

lemma coloredSet_pairCount {n : ℕ} (ρ : Fin n ≃ F) (B : α → Finset H) (ω : Fin n → α)
    (t s : F) (q : H) :
    (pairCount (coloredSet ρ B ω) (coloredSet ρ B ω) ((t,s),q):ℝ)=
      rootSum ρ (fun i j ↦ coarseKernel B q (ω i) (ω j)) t s := by
  rw [coloredSet,assembly_pairCount _
    (fun _ _ hij ↦ parallelCurve_disjoint (fun he ↦ hij (ρ.injective he)))]
  simp_rw [parallelCurve_pairCount]
  push_cast
  unfold rootSum coarseKernel
  simp only [mul_comm]

/-- An actual-set theorem without a maximum-kernel or origin-repair cost.
The ambient fine group is completely partitioned before selecting colors. -/
theorem exists_actual_color_budget {n : ℕ} (ρ : Fin n ≃ F) (hF : ringChar F≠2)
    (B : α → Finset H) (S : Finset H) (w : H → ℝ) (hw : ∀ q∈S, 0≤w q) :
    ∃ ω : Fin n → α, ∀ q∈S, ∀ t s : F,
      w q*((pairCount (coloredSet ρ B ω) (coloredSet ρ B ω) ((t,s),q):ℝ)-
        (n:ℝ)^2*kernelMean (coarseKernel B q))^2≤
      4*(n:ℝ)*kernelBudget n S (coarseKernel B) w := by
  obtain ⟨ω,hω⟩ := exists_root_budget ρ hF S (coarseKernel B)
    (fun q hq ↦ coarseKernel_symm B q) w hw
  refine ⟨ω,fun q hq t s ↦ ?_⟩
  rw [coloredSet_pairCount]
  exact hω q hq t s

end Erdos66CompletePartitionColorTransfer
