import Submission.UniversalKernelAccuracyExplore
import Submission.MixedDisjointAssemblyExplore

/-! Universal fine palettes formulated before any coarse ambient group.
All later real kernels are covered; symmetry is not required. -/
namespace Erdos66UniversalPaletteMatrix
open Erdos66UniversalColorKernelSpan Erdos66DisjointCurvePalette
  Erdos66OriginRepair Erdos66ParabolaRepair Erdos66DisjointPaletteAssembly
  Erdos66UniformColorMoments Erdos66FiniteLabelRootTransfer
  Erdos66UniversalActualKernel Erdos66UniversalKernelAccuracy
open scoped Classical
set_option maxHeartbeats 2600000

variable {p : ℕ} [Fact p.Prime]
variable {α : Type*} [Fintype α] [Nonempty α] [DecidableEq α]

noncomputable def paletteSum {h : ℕ} (P : Fin h → Finset (ZMod p×ZMod p))
    (ω : Fin h → α) (K : α → α → ℝ) (z : ZMod p×ZMod p) : ℝ :=
  ∑ i : Fin h, ∑ j : Fin h, K (ω i) (ω j)*(pairCount (P i) (P j) z:ℝ)

/-- The palette precedes every later, possibly nonsymmetric, real kernel. -/
theorem exists_universal_palette_matrix_bound (hp : p≠2) (h m : ℕ)
    (hh : h^2+4*h+2<p) (e : Fin h ≃ α×Fin m) :
    ∃ P : Fin h → Finset (ZMod p×ZMod p),
      Pairwise (fun i j ↦ Disjoint (P i) (P j)) ∧
      ∀ (K : α → α → ℝ) (M : ℝ), 0 ≤ M → (∀ x y, |K x y| ≤ M) →
        ∀ t s : ZMod p,
        (paletteSum P (fun i ↦ (e i).1) K (t,s)-(h:ℝ)^2*kernelMean K)^2 ≤
          2*(M*(10*(h:ℝ)+8))^2+32*(h:ℝ)^3*(∑ z : α×α, (K z.1 z.2)^2) := by
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
  refine ⟨P,hP,fun K M hM hK t s ↦ ?_⟩
  have hfirst := weighted_matrix_error P (fun i ↦ curve (u i))
    (fun i j ↦ K (e i).1 (e j).1) M (10*(h:ℝ)+8) hM
    (fun i j ↦ hK (e i).1 (e j).1) (t,s) (hL (t,s))
  simp_rw [curve_pairCount] at hfirst
  change |paletteSum P (fun i ↦ (e i).1) K (t,s)-
    labelRootCount h a (fun i j ↦ K (e i).1 (e j).1) t s| ≤ _ at hfirst
  have hfirstSq := pow_le_pow_left₀ (abs_nonneg _) hfirst 2
  rw [sq_abs] at hfirstSq
  have hsecond := hroot K t s
  nlinarith [sq_nonneg
    ((paletteSum P (fun i ↦ (e i).1) K (t,s)-
       labelRootCount h a (fun i j ↦ K (e i).1 (e j).1) t s)-
     (labelRootCount h a (fun i j ↦ K (e i).1 (e j).1) t s-
       (h:ℝ)^2*kernelMean K))]

/-- Nonnegative matrices admit a relative estimate, even when their mean is
zero. No family of coarse sets is needed in this formulation. -/
theorem exists_universal_palette_relative_sq (hp : p≠2) (h m : ℕ)
    (hh : h^2+4*h+2<p) (e : Fin h ≃ α×Fin m) :
    ∃ P : Fin h → Finset (ZMod p×ZMod p),
      Pairwise (fun i j ↦ Disjoint (P i) (P j)) ∧
      ∀ (K : α → α → ℝ), (∀ x y, 0 ≤ K x y) → ∀ t s : ZMod p,
        (paletteSum P (fun i ↦ (e i).1) K (t,s)-(h:ℝ)^2*kernelMean K)^2 ≤
          (Fintype.card α:ℝ)^4*(2*(10*(h:ℝ)+8)^2+32*(h:ℝ)^3)*(kernelMean K)^2 := by
  obtain ⟨P,hP,hbound⟩ := exists_universal_palette_matrix_bound hp h m hh e
  refine ⟨P,hP,fun K hK t s ↦ ?_⟩
  have hmu := kernelMean_nonneg K hK
  have he := hbound K ((Fintype.card α:ℝ)^2*kernelMean K) (by positivity)
    (fun x y ↦ by rw [abs_of_nonneg (hK x y)]; exact kernel_le_total_mean K hK x y) t s
  have hs := mul_le_mul_of_nonneg_left (kernel_second_le_mean_sq K hK)
    (show 0 ≤ 32*(h:ℝ)^3 by positivity)
  nlinarith only [he,hs]

theorem exists_universal_palette_accuracy (hp : p≠2) (h m : ℕ)
    (hh : h^2+4*h+2<p) (e : Fin h ≃ α×Fin m) (hpos : 1 ≤ h)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hsize : 680*(Fintype.card α:ℝ)^4 ≤ ε^2*(h:ℝ)) :
    ∃ P : Fin h → Finset (ZMod p×ZMod p),
      Pairwise (fun i j ↦ Disjoint (P i) (P j)) ∧
      ∀ (K : α → α → ℝ), (∀ x y, 0 ≤ K x y) → ∀ t s : ZMod p,
        |paletteSum P (fun i ↦ (e i).1) K (t,s)-(h:ℝ)^2*kernelMean K| ≤
          ε*(h:ℝ)^2*kernelMean K := by
  obtain ⟨P,hP,hbound⟩ := exists_universal_palette_relative_sq hp h m hh e
  refine ⟨P,hP,fun K hK t s ↦ ?_⟩
  have hmu := kernelMean_nonneg K hK
  have he := hbound K hK t s
  have hc := mul_le_mul_of_nonneg_left (repair_root_coefficient_le h hpos)
    (show 0 ≤ (Fintype.card α:ℝ)^4 by positivity)
  have hc' := mul_le_mul_of_nonneg_right hc (sq_nonneg (kernelMean K))
  have hscale := mul_le_mul_of_nonneg_right hsize
    (show 0 ≤ (h:ℝ)^3*(kernelMean K)^2 by positivity)
  have hsq : (paletteSum P (fun i ↦ (e i).1) K (t,s)-(h:ℝ)^2*kernelMean K)^2 ≤
      (ε*(h:ℝ)^2*kernelMean K)^2 := by nlinarith only [he,hc',hscale]
  exact (sq_le_sq₀ (abs_nonneg _) (by positivity)).mp (by simpa only [sq_abs] using hsq)

end Erdos66UniversalPaletteMatrix
