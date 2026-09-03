import Submission.UniversalColorKernelSpanExplore
import Submission.ActualColorRootTransferExplore

/-! One disjoint palette and one balanced coloring precede all later coarse
sets and all their targets. The price depends on the fixed color alphabet,
not on the number of coarse targets. -/
namespace Erdos66UniversalActualKernel
open Erdos66UniversalColorKernelSpan Erdos66ActualColorRootTransfer
  Erdos66DisjointCurvePalette Erdos66OriginRepair Erdos66ParabolaRepair
  Erdos66DisjointPaletteAssembly Erdos66UniformColorMoments Erdos66UniformSelection
  Erdos66FiniteLabelRootTransfer
open scoped Classical
set_option maxHeartbeats 2600000

variable {p : ℕ} [Fact p.Prime]
variable {α H : Type*} [Fintype α] [Nonempty α] [DecidableEq α]
  [AddCommGroup H] [DecidableEq H]

/-- No finite list of coarse targets or target weights is needed. -/
theorem exists_universal_actual_kernel_bound (hp : p≠2) (h m : ℕ)
    (hh : h^2+4*h+2<p) (e : Fin h ≃ α×Fin m) :
    ∃ (a : ZMod p) (P : Fin h → Finset (ZMod p×ZMod p)),
      (∀ i<h, a+(i:ZMod p)≠0) ∧ (∀ q<2*h, 2*a+(q:ZMod p)≠0) ∧
      Pairwise (fun i j ↦ Disjoint (P i) (P j)) ∧
      ∀ (B : α → Finset H) (q : H) (M : ℝ), 0 ≤ M →
        (∀ x y, coarseKernel B q x y ≤ M) → ∀ t s : ZMod p,
        ((pairCount (assembly P (fun i ↦ B (e i).1))
          (assembly P (fun i ↦ B (e i).1)) ((t,s),q):ℝ)-
          (h:ℝ)^2*kernelMean (coarseKernel B q))^2 ≤
          2*(M*(10*(h:ℝ)+8))^2+
            32*(h:ℝ)^3*(∑ z : α×α, (coarseKernel B q z.1 z.2)^2) := by
  obtain ⟨a,ha,hop,hroot⟩ := exists_all_balanced_kernels hp h m (by omega) e
  let u : Fin h → ZMod p := fun i ↦ a+(i.val:ZMod p)
  have hu : Function.Injective u := by
    intro i j hij
    apply Fin.ext
    have hi := Erdos66PolynomialMixedEnergy.natCast_injOn_range p h (by omega)
    apply hi (Finset.mem_range.mpr i.isLt) (Finset.mem_range.mpr j.isLt)
    exact add_left_cancel hij
  have hu0 (i : Fin h) : u i≠0 := ha i.val i.isLt
  have huopp (i j : Fin h) : u i+u j≠0 := by
    have hs : i.val+j.val<2*h := by have := i.isLt; have := j.isLt; omega
    have he : u i+u j=2*a+((i.val+j.val:ℕ):ZMod p) := by dsimp [u]; push_cast; ring
    rw [he]
    exact hop _ hs
  obtain ⟨P,hP,hL⟩ := exists_disjoint_curve_palette h
    (by rw [ZMod.card]; omega) (by rw [ZMod.card]; omega)
    (by simpa only [ZMod.ringChar_zmod_n] using hp) u hu hu0 huopp
  refine ⟨a,P,ha,hop,hP,fun B q M hM hB t s ↦ ?_⟩
  have hfirst := assembly_root_error h a P hP hL B (fun i ↦ (e i).1) q M hM hB t s
  have hfirstSq := pow_le_pow_left₀ (abs_nonneg _) hfirst 2
  rw [sq_abs] at hfirstSq
  have hsecond := hroot (coarseKernel B q) t s
  nlinarith [sq_nonneg
    (((pairCount (assembly P (fun i ↦ B (e i).1))
      (assembly P (fun i ↦ B (e i).1)) ((t,s),q):ℝ)-
       labelRootCount h a (fun i j ↦ coarseKernel B q (e i).1 (e j).1) t s)-
     (labelRootCount h a (fun i j ↦ coarseKernel B q (e i).1 (e j).1) t s-
       (h:ℝ)^2*kernelMean (coarseKernel B q)))]

lemma kernelMean_nonneg (K : α → α → ℝ) (hK : ∀ x y, 0 ≤ K x y) : 0 ≤ kernelMean K := by
  unfold kernelMean mean
  exact div_nonneg (Finset.sum_nonneg (fun z hz ↦ hK z.1 z.2)) (Nat.cast_nonneg _)

lemma kernel_le_total_mean (K : α → α → ℝ) (hK : ∀ x y, 0 ≤ K x y) (x y : α) :
    K x y ≤ (Fintype.card α:ℝ)^2*kernelMean K := by
  have hsum := Finset.single_le_sum (s := Finset.univ)
    (f := fun z : α×α ↦ K z.1 z.2) (fun z hz ↦ hK z.1 z.2) (Finset.mem_univ (x,y))
  have hc : (Fintype.card α:ℝ)≠0 := by exact_mod_cast Fintype.card_ne_zero
  unfold kernelMean mean
  rw [Fintype.card_prod,Nat.cast_mul]
  have he : (Fintype.card α:ℝ)^2*((∑ z : α×α, K z.1 z.2)/
      ((Fintype.card α:ℝ)*(Fintype.card α:ℝ)))=∑ z : α×α, K z.1 z.2 := by field_simp
  rwa [he]

lemma kernel_second_le_mean_sq (K : α → α → ℝ) (hK : ∀ x y, 0 ≤ K x y) :
    (∑ z : α×α, (K z.1 z.2)^2) ≤ (Fintype.card α:ℝ)^4*(kernelMean K)^2 := by
  have he := Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ)
    (fun z : α×α ↦ fun hz ↦ hK z.1 z.2)
  have hc : (Fintype.card α:ℝ)≠0 := by exact_mod_cast Fintype.card_ne_zero
  have hm : (∑ z : α×α, K z.1 z.2)=(Fintype.card α:ℝ)^2*kernelMean K := by
    unfold kernelMean mean
    rw [Fintype.card_prod,Nat.cast_mul]
    field_simp
  rw [hm] at he
  convert he using 1 <;> ring

/-- Nonnegative coarse counts automatically satisfy the needed norm bounds.
The loss is now the fourth power of the fixed color cardinality. -/
theorem exists_universal_actual_relative_sq (hp : p≠2) (h m : ℕ)
    (hh : h^2+4*h+2<p) (e : Fin h ≃ α×Fin m) :
    ∃ P : Fin h → Finset (ZMod p×ZMod p),
      Pairwise (fun i j ↦ Disjoint (P i) (P j)) ∧
      ∀ (B : α → Finset H) (q : H) (t s : ZMod p),
        ((pairCount (assembly P (fun i ↦ B (e i).1))
          (assembly P (fun i ↦ B (e i).1)) ((t,s),q):ℝ)-
          (h:ℝ)^2*kernelMean (coarseKernel B q))^2 ≤
          (Fintype.card α:ℝ)^4*(2*(10*(h:ℝ)+8)^2+32*(h:ℝ)^3)*
            (kernelMean (coarseKernel B q))^2 := by
  obtain ⟨a,P,ha,hop,hP,hbound⟩ := exists_universal_actual_kernel_bound (H := H) hp h m hh e
  refine ⟨P,hP,fun B q t s ↦ ?_⟩
  have hnonneg := coarseKernel_nonneg B q
  have hmu := kernelMean_nonneg (coarseKernel B q) hnonneg
  have he := hbound B q ((Fintype.card α:ℝ)^2*kernelMean (coarseKernel B q))
    (by positivity) (kernel_le_total_mean (coarseKernel B q) hnonneg) t s
  have hs := mul_le_mul_of_nonneg_left (kernel_second_le_mean_sq (coarseKernel B q) hnonneg)
    (show 0 ≤ 32*(h:ℝ)^3 by positivity)
  nlinarith only [he,hs]

end Erdos66UniversalActualKernel
