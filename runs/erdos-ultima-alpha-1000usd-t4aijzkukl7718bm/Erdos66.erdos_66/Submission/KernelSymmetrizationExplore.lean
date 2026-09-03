import Submission.UniformGraphColorTransferExplore

/-! Symmetrization loses no information for symmetric label-sum fibers.
This extends the color-energy expectation bound to arbitrary real kernels. -/
namespace Erdos66KernelSymmetrization
open Erdos66UniformSelection Erdos66UniformColorMoments Erdos66CenteredColorSelection
  Erdos66CompletePartitionColorTransfer Erdos66FiberColorEnergy
open scoped Classical
set_option maxHeartbeats 2800000
variable {α : Type*} [Fintype α] [Nonempty α] [DecidableEq α]

noncomputable def symKernel (K : α → α → ℝ) (x y : α) : ℝ := (K x y+K y x)/2

omit [Nonempty α] [DecidableEq α] in
lemma kernelMean_transpose (K : α → α → ℝ) : kernelMean (fun x y ↦ K y x)=kernelMean K := by
  simp only [kernelMean,mean,Fintype.sum_prod_type]
  rw [Finset.sum_comm]

lemma kernelMean_sym (K : α → α → ℝ) : kernelMean (symKernel K)=kernelMean K := by
  have ht := kernelMean_transpose K
  unfold kernelMean mean at ht ⊢
  simp only [symKernel,←Finset.sum_div,Finset.sum_add_distrib]
  field_simp at ht ⊢
  linarith

omit [Fintype α] [Nonempty α] [DecidableEq α] in
lemma symKernel_symm (K : α → α → ℝ) (x y : α) : symKernel K x y=symKernel K y x := by
  simp only [symKernel,add_comm]

lemma centered_sym (K : α → α → ℝ) (x y : α) :
    centeredKernel (symKernel K) x y=(centeredKernel K x y+centeredKernel K y x)/2 := by
  simp only [centeredKernel,kernelMean_sym,symKernel]
  ring

lemma diagonal_sym (K : α → α → ℝ) : diagonalCenteredSecond (symKernel K)=diagonalCenteredSecond K := by
  unfold diagonalCenteredSecond
  congr 1
  funext x
  rw [centered_sym]
  congr 1
  ring

lemma variance_sym_le (K : α → α → ℝ) : colorVariance (symKernel K)≤colorVariance K := by
  have ht := kernelMean_transpose (fun x y ↦ (centeredKernel K x y)^2)
  have he : kernelMean (fun x y ↦ ((centeredKernel K x y)^2+(centeredKernel K y x)^2)/2)=
      colorVariance K := by
    unfold colorVariance
    unfold kernelMean mean at ht ⊢
    simp only [←Finset.sum_div,Finset.sum_add_distrib]
    field_simp at ht ⊢
    linarith
  rw [←he]
  apply mean_mono
  intro x
  change (centeredKernel (symKernel K) x.1 x.2)^2≤_
  rw [centered_sym]
  nlinarith [sq_nonneg (centeredKernel K x.1 x.2-centeredKernel K x.2 x.1)]

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

omit [Fintype F] in
lemma fiber_transpose {n : ℕ} (ρ : Fin n ≃ F) (V : Fin n → Fin n → ℝ) (q : F) :
    fiber n (fun i j ↦ ρ i+ρ j) (fun i j ↦ V j i) q=
      fiber n (fun i j ↦ ρ i+ρ j) V q := by
  unfold fiber
  simp only [Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  simp only [add_comm]

lemma fiber_sym {n : ℕ} (ρ : Fin n ≃ F) (K : α → α → ℝ) (ω : Fin n → α) (q : F) :
    fiber n (fun i j ↦ ρ i+ρ j) (fun i j ↦ centeredKernel (symKernel K) (ω i) (ω j)) q=
      fiber n (fun i j ↦ ρ i+ρ j) (fun i j ↦ centeredKernel K (ω i) (ω j)) q := by
  have ht := fiber_transpose ρ (fun i j ↦ centeredKernel K (ω i) (ω j)) q
  unfold fiber at ht ⊢
  simp_rw [centered_sym]
  have hi (e : Fin n×Fin n) :
      (if ρ e.1+ρ e.2=q then (centeredKernel K (ω e.1) (ω e.2)+centeredKernel K (ω e.2) (ω e.1))/2 else 0)=
        ((if ρ e.1+ρ e.2=q then centeredKernel K (ω e.1) (ω e.2) else 0)+
          (if ρ e.1+ρ e.2=q then centeredKernel K (ω e.2) (ω e.1) else 0))/2 := by
    split_ifs <;> ring
  simp_rw [hi]
  rw [←Finset.sum_div,Finset.sum_add_distrib,ht]
  ring

lemma colorEnergy_sym {n : ℕ} (ρ : Fin n ≃ F) (K : α → α → ℝ) (ω : Fin n → α) :
    colorEnergy ρ (symKernel K) ω=colorEnergy ρ K ω := by
  simp only [colorEnergy,energy,fiber_sym]

/-- The symmetry assumption on the later kernel can be dropped: only its
symmetric part enters the actual label-sum fibers, and symmetrization
contracts variance while preserving the diagonal centered second moment. -/
theorem mean_colorEnergy_le_general {n : ℕ} (ρ : Fin n ≃ F) (hF : ringChar F≠2)
    (K : α → α → ℝ) :
    mean (colorEnergy ρ K)≤8*(n:ℝ)^2*colorVariance K+2*(n:ℝ)*diagonalCenteredSecond K := by
  have hh := mean_colorEnergy_le ρ hF (symKernel K) (symKernel_symm K)
  have he : colorEnergy ρ (symKernel K)=colorEnergy ρ K := funext (colorEnergy_sym ρ K)
  rw [he,diagonal_sym] at hh
  have hm := mul_le_mul_of_nonneg_left (variance_sym_le K)
    (show (0:ℝ)≤8*(n:ℝ)^2 by positivity)
  exact hh.trans (by linarith)

end Erdos66KernelSymmetrization
