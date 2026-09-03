import Submission.UniformMatrixSpanExplore
import Submission.FiniteLabelRootTransferExplore
import Submission.UniformColorMomentsExplore

/-! A fixed finite color alphabet makes all later pair kernels a single
finite-dimensional space. Translation selection therefore needs no finite
list of coarse targets, at an explicit color-dimension cost. -/
namespace Erdos66UniversalColorKernelSpan
open Erdos66UniformMatrixSpan Erdos66PairWeightedCharacterEnergy
  Erdos66PairWeightedRootTransfer Erdos66FiniteLabelRootTransfer
  Erdos66UniformColorMoments Erdos66UniformSelection
open scoped Classical
set_option maxHeartbeats 2200000

variable {α : Type*} [Fintype α] [Nonempty α] [DecidableEq α]

noncomputable def colorMask (col : ℕ → α) (q : α×α) (i j : ℕ) : ℝ :=
  if (col i,col j)=q then 1 else 0

lemma colorMask_combination (col : ℕ → α) (K : α → α → ℝ) :
    matrixCombination Finset.univ (colorMask col) (fun q ↦ K q.1 q.2)=
      fun i j ↦ K (col i) (col j) := by
  funext i j
  simp [matrixCombination,colorMask]

lemma colorMask_total_mass (h : ℕ) (col : ℕ → α) :
    (∑ q : α×α, matrixMass h (colorMask col q))=(h:ℝ)^2 := by
  unfold matrixMass
  rw [Finset.sum_comm]
  have he (i : ℕ) : (∑ q : α×α, ∑ j∈Finset.range h, (colorMask col q i j)^2)=
      ∑ j∈Finset.range h, ∑ q : α×α, (colorMask col q i j)^2 := Finset.sum_comm
  simp_rw [he]
  have hm (i j : ℕ) : (∑ q : α×α, (colorMask col q i j)^2)=1 := by
    simp [colorMask]
  simp_rw [hm]
  simp [pow_two]

variable {p : ℕ} [Fact p.Prime]

/-- No symmetry or positivity restriction on later kernels is required. -/
theorem exists_all_color_kernels (hp : p≠2) (h : ℕ) (hh : 4*h<p) (col : ℕ → α) :
    ∃ a : ZMod p,
      (∀ i<h, a+(i:ZMod p)≠0) ∧ (∀ q<2*h, 2*a+(q:ZMod p)≠0) ∧
      ∀ K : α → α → ℝ, ∀ t s : ZMod p,
        (matrixRootCount h a (fun i j ↦ K (col i) (col j)) t s-
          matrixSum h (fun i j ↦ K (col i) (col j)))^2 ≤
          16*(h:ℝ)^3*(∑ q : α×α, (K q.1 q.2)^2) := by
  obtain ⟨a,ha,hop,hspan⟩ := exists_uniform_matrix_span hp h hh Finset.univ (colorMask col)
  refine ⟨a,ha,hop,fun K t s ↦ ?_⟩
  have he := hspan (fun q ↦ K q.1 q.2) t s
  rw [colorMask_combination,colorMask_total_mass] at he
  convert he using 1 <;> ring

noncomputable def extendColor {h : ℕ} (ω : Fin h → α) (i : ℕ) : α :=
  if hi : i<h then ω ⟨i,hi⟩ else Classical.arbitrary α

lemma extendColor_fin {h : ℕ} (ω : Fin h → α) (i : Fin h) :
    extendColor ω i.val=ω i := by simp [extendColor,i.isLt]

lemma matrixSum_color {h : ℕ} (ω : Fin h → α) (K : α → α → ℝ) :
    matrixSum h (fun i j ↦ K (extendColor ω i) (extendColor ω j))=
      ∑ i : Fin h, ∑ j : Fin h, K (ω i) (ω j) := by
  unfold matrixSum
  rw [←sum_fin_pair]
  simp_rw [extendColor_fin]

lemma matrixRootCount_color {h : ℕ} (a : ZMod p) (ω : Fin h → α) (K : α → α → ℝ)
    (t s : ZMod p) :
    matrixRootCount h a (fun i j ↦ K (extendColor ω i) (extendColor ω j)) t s=
      labelRootCount h a (fun i j ↦ K (ω i) (ω j)) t s := by
  unfold matrixRootCount labelRootCount
  rw [←sum_fin_pair]
  simp_rw [extendColor_fin]

/-- Fixed coloring, then one translation, then ALL later kernels. -/
theorem exists_all_label_color_kernels (hp : p≠2) (h : ℕ) (hh : 4*h<p) (ω : Fin h → α) :
    ∃ a : ZMod p,
      (∀ i<h, a+(i:ZMod p)≠0) ∧ (∀ q<2*h, 2*a+(q:ZMod p)≠0) ∧
      ∀ K : α → α → ℝ, ∀ t s : ZMod p,
        (labelRootCount h a (fun i j ↦ K (ω i) (ω j)) t s-
          (∑ i : Fin h, ∑ j : Fin h, K (ω i) (ω j)))^2 ≤
          16*(h:ℝ)^3*(∑ q : α×α, (K q.1 q.2)^2) := by
  obtain ⟨a,ha,hop,he⟩ := exists_all_color_kernels hp h hh (extendColor ω)
  refine ⟨a,ha,hop,fun K t s ↦ ?_⟩
  simpa only [matrixSum_color,matrixRootCount_color] using he K t s

/-- Equal color multiplicities make the unsigned mean exact for every kernel. -/
lemma balanced_kernel_sum {h m : ℕ} (e : Fin h ≃ α×Fin m) (K : α → α → ℝ) :
    (∑ i : Fin h, ∑ j : Fin h, K (e i).1 (e j).1)=(h:ℝ)^2*kernelMean K := by
  have hs : (∑ i : Fin h, ∑ j : Fin h, K (e i).1 (e j).1)=
      (m:ℝ)^2*∑ q : α×α, K q.1 q.2 := by
    have hinner (a : α) : (∑ j : Fin h, K a (e j).1)=
        ∑ z : α×Fin m, K a z.1 := e.sum_comp (fun z ↦ K a z.1)
    rw [e.sum_comp (fun z ↦ ∑ j : Fin h, K z.1 (e j).1)]
    simp_rw [hinner]
    simp only [Fintype.sum_prod_type,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    simp only [←Finset.mul_sum]
    ring
  have hc : h=Fintype.card α*m := by
    simpa only [Fintype.card_fin,Fintype.card_prod] using Fintype.card_congr e
  rw [hs,hc]
  unfold kernelMean mean
  rw [Fintype.card_prod]
  push_cast
  have ha : (Fintype.card α:ℝ)≠0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp

/-- The same translation handles every later kernel with exact uniform
color mean. The color dimension is visible in its unnormalized L2 norm. -/
theorem exists_all_balanced_kernels (hp : p≠2) (h m : ℕ) (hh : 4*h<p)
    (e : Fin h ≃ α×Fin m) :
    ∃ a : ZMod p,
      (∀ i<h, a+(i:ZMod p)≠0) ∧ (∀ q<2*h, 2*a+(q:ZMod p)≠0) ∧
      ∀ K : α → α → ℝ, ∀ t s : ZMod p,
        (labelRootCount h a (fun i j ↦ K (e i).1 (e j).1) t s-
          (h:ℝ)^2*kernelMean K)^2 ≤
          16*(h:ℝ)^3*(∑ q : α×α, (K q.1 q.2)^2) := by
  obtain ⟨a,ha,hop,he⟩ := exists_all_label_color_kernels hp h hh (fun i ↦ (e i).1)
  refine ⟨a,ha,hop,fun K t s ↦ ?_⟩
  simpa only [balanced_kernel_sum] using he K t s

end Erdos66UniversalColorKernelSpan
