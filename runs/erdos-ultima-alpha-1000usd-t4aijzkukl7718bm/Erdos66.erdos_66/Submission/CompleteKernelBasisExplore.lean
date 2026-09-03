import Submission.KernelSymmetrizationExplore

/-! Ordered matrix masks have a bounded total centered variance, uniformly
in the size of the color alphabet. A single finite-dimensional selection
therefore controls all later real kernels for a complete graph partition. -/
namespace Erdos66CompleteKernelBasis
open Erdos66UniformSelection Erdos66UniformColorMoments Erdos66CenteredColorSelection
  Erdos66CompletePartitionColorTransfer Erdos66FiberColorEnergy
  Erdos66KernelSymmetrization Erdos66FixedPatternColorEnergy
open scoped Classical
set_option maxHeartbeats 2800000
variable {α : Type*} [Fintype α] [Nonempty α] [DecidableEq α]

noncomputable def mask (q : α×α) (x y : α) : ℝ := if (x,y)=q then 1 else 0

omit [Nonempty α] in
lemma mask_mean (q : α×α) : kernelMean (mask q)=1/(Fintype.card (α×α):ℝ) := by
  simp [kernelMean,mean,mask]

omit [Nonempty α] in
lemma mask_combination (K : α → α → ℝ) (x y : α) :
    (∑ q : α×α, K q.1 q.2*mask q x y)=K x y := by simp [mask]

omit [Nonempty α] in
lemma mask_mean_combination (K : α → α → ℝ) :
    (∑ q : α×α, K q.1 q.2*kernelMean (mask q))=kernelMean K := by
  simp_rw [mask_mean]
  simp only [kernelMean,mean,mul_one_div,Finset.sum_div]

lemma centered_mask_combination (K : α → α → ℝ) (x y : α) :
    (∑ q : α×α, K q.1 q.2*centeredKernel (mask q) x y)=centeredKernel K x y := by
  simp only [centeredKernel,mul_sub,Finset.sum_sub_distrib,mask_combination,mask_mean_combination]

omit [Nonempty α] in
lemma mask_sq_sum (x y : α) : (∑ q : α×α, (mask q x y)^2)=1 := by simp [mask]

omit [Nonempty α] in
lemma mask_sum (x y : α) : (∑ q : α×α, mask q x y)=1 := by simp [mask]

lemma centered_mask_sq_sum (x y : α) :
    (∑ q : α×α, (centeredKernel (mask q) x y)^2)=1-1/(Fintype.card (α×α):ℝ) := by
  have hc : (Fintype.card (α×α):ℝ)≠0 := by exact_mod_cast Fintype.card_ne_zero
  have hi (q : α×α) : (centeredKernel (mask q) x y)^2=
      (mask q x y)^2+(-2/(Fintype.card (α×α):ℝ))*mask q x y+
        (1/(Fintype.card (α×α):ℝ))^2 := by
    simp only [centeredKernel,mask_mean]
    ring
  simp_rw [hi]
  rw [Finset.sum_add_distrib,Finset.sum_add_distrib,←Finset.mul_sum,mask_sum,mask_sq_sum]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one]
  field_simp
  ring

lemma centered_mask_sq_sum_le (x y : α) : (∑ q : α×α, (centeredKernel (mask q) x y)^2)≤1 := by
  rw [centered_mask_sq_sum]
  have hh : 0≤1/(Fintype.card (α×α):ℝ) := by positivity
  linarith

lemma total_mask_variance_le : (∑ q : α×α, colorVariance (mask q))≤1 := by
  unfold colorVariance kernelMean
  rw [←mean_sum]
  have hh := mean_mono (fun p : α×α ↦ ∑ q : α×α, (centeredKernel (mask q) p.1 p.2)^2)
    (fun _ ↦ 1) (fun p ↦ centered_mask_sq_sum_le p.1 p.2)
  simpa only [mean_const] using hh

lemma total_mask_diagonal_le : (∑ q : α×α, diagonalCenteredSecond (mask q))≤1 := by
  unfold diagonalCenteredSecond
  rw [←mean_sum]
  have hh := mean_mono (fun p : α ↦ ∑ q : α×α, (centeredKernel (mask q) p p)^2)
    (fun _ ↦ 1) (fun p ↦ centered_mask_sq_sum_le p p)
  simpa only [mean_const] using hh

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

lemma exists_total_basis_energy {n : ℕ} (ρ : Fin n ≃ F) (hF : ringChar F≠2) :
    ∃ ω : Fin n → α,
      (∑ q : α×α, Erdos66CompletePartitionColorTransfer.colorEnergy ρ (mask q) ω)≤8*(n:ℝ)^2+2*n := by
  obtain ⟨ω,hω⟩ := exists_le_mean (fun ω : Fin n → α ↦
    ∑ q : α×α, Erdos66CompletePartitionColorTransfer.colorEnergy ρ (mask q) ω)
  refine ⟨ω,hω.trans ?_⟩
  rw [mean_sum]
  calc
    _ ≤ ∑ q : α×α, (8*(n:ℝ)^2*colorVariance (mask q)+2*n*diagonalCenteredSecond (mask q)) :=
      Finset.sum_le_sum (fun q _ ↦ mean_colorEnergy_le_general ρ hF (mask q))
    _ = 8*(n:ℝ)^2*(∑ q : α×α, colorVariance (mask q))+
        2*n*(∑ q : α×α, diagonalCenteredSecond (mask q)) := by
      rw [Finset.sum_add_distrib,←Finset.mul_sum,←Finset.mul_sum]
    _ ≤ _ := by
      have h1 := mul_le_mul_of_nonneg_left (total_mask_variance_le (α := α))
        (show (0:ℝ)≤8*(n:ℝ)^2 by positivity)
      have h2 := mul_le_mul_of_nonneg_left (total_mask_diagonal_le (α := α))
        (show (0:ℝ)≤2*n by positivity)
      nlinarith

omit [Fintype F] in
lemma fiber_mask_combination {n : ℕ} (ρ : Fin n ≃ F) (K : α → α → ℝ)
    (ω : Fin n → α) (u : F) :
    fiber n (fun i j ↦ ρ i+ρ j) (fun i j ↦ centeredKernel K (ω i) (ω j)) u=
      ∑ q : α×α, K q.1 q.2*
        fiber n (fun i j ↦ ρ i+ρ j) (fun i j ↦ centeredKernel (mask q) (ω i) (ω j)) u := by
  unfold fiber
  simp_rw [←centered_mask_combination K]
  have hi (e : Fin n×Fin n) :
      (if ρ e.1+ρ e.2=u then ∑ q : α×α, K q.1 q.2*centeredKernel (mask q) (ω e.1) (ω e.2) else 0)=
        ∑ q : α×α, K q.1 q.2*
          (if ρ e.1+ρ e.2=u then centeredKernel (mask q) (ω e.1) (ω e.2) else 0) := by
    by_cases he : ρ e.1+ρ e.2=u <;> simp only [he,if_true,if_false,mul_zero,Finset.sum_const_zero]
  simp_rw [hi]
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum]

lemma colorEnergy_mask_bound {n : ℕ} (ρ : Fin n ≃ F) (K : α → α → ℝ) (ω : Fin n → α) :
    Erdos66CompletePartitionColorTransfer.colorEnergy ρ K ω≤
      (∑ q : α×α, (K q.1 q.2)^2)*
        (∑ q : α×α, Erdos66CompletePartitionColorTransfer.colorEnergy ρ (mask q) ω) := by
  unfold Erdos66CompletePartitionColorTransfer.colorEnergy energy
  simp_rw [fiber_mask_combination ρ K]
  calc
    _ ≤ ∑ u : F, (∑ q : α×α, (K q.1 q.2)^2)*
        (∑ q : α×α,
          (fiber n (fun i j ↦ ρ i+ρ j) (fun i j ↦ centeredKernel (mask q) (ω i) (ω j)) u)^2) := by
      apply Finset.sum_le_sum
      intro u hu
      exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ _ _
    _ = _ := by rw [←Finset.mul_sum,Finset.sum_comm]

lemma colorEnergy_centered {n : ℕ} (ρ : Fin n ≃ F) (K : α → α → ℝ) (ω : Fin n → α) :
    Erdos66CompletePartitionColorTransfer.colorEnergy ρ (centeredKernel K) ω=
      Erdos66CompletePartitionColorTransfer.colorEnergy ρ K ω := by
  simp only [Erdos66CompletePartitionColorTransfer.colorEnergy,centeredKernel,kernelMean_centered,sub_zero]

/-- One coloring precedes every later real kernel. There is no finite
coarse-target list or number-of-kernels factor. The unnormalized centered
matrix norm retains the actual color-dimension cost. -/
theorem exists_universal_centered_energy {n : ℕ} (ρ : Fin n ≃ F) (hF : ringChar F≠2) :
    ∃ ω : Fin n → α, ∀ K : α → α → ℝ,
      Erdos66CompletePartitionColorTransfer.colorEnergy ρ K ω≤
        (8*(n:ℝ)^2+2*n)*(∑ q : α×α, (centeredKernel K q.1 q.2)^2) := by
  obtain ⟨ω,hω⟩ := exists_total_basis_energy (α := α) ρ hF
  refine ⟨ω,fun K ↦ ?_⟩
  have he := colorEnergy_mask_bound ρ (centeredKernel K) ω
  rw [colorEnergy_centered] at he
  have hm := mul_le_mul_of_nonneg_left hω
    (show 0≤∑ q : α×α, (centeredKernel K q.1 q.2)^2 from Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _))
  exact he.trans (by simpa only [mul_comm] using hm)

end Erdos66CompleteKernelBasis
