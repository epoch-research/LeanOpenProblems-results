import Submission.DisjointCurvePaletteExplore
import Submission.FixedTranslateColorRootExplore

/-! Actual-set transfer for coarse color kernels. The fine palette and field
translate precede the coarse colors; one later color assignment controls
all fine targets over a finite list of coarse targets. -/
namespace Erdos66ActualColorRootTransfer
open Erdos66OriginRepair Erdos66ParabolaRepair Erdos66DisjointPaletteAssembly
  Erdos66DisjointCurvePalette Erdos66UniformColorMoments Erdos66CenteredColorSelection
  Erdos66FiniteLabelRootTransfer Erdos66FixedTranslateColorRoot
open scoped Classical
set_option maxHeartbeats 2600000

variable {p : ℕ} [Fact p.Prime]
variable {α H : Type*} [Fintype α] [Nonempty α] [DecidableEq α]
  [AddCommGroup H] [DecidableEq H]

noncomputable def coarseKernel (B : α → Finset H) (q : H) (x y : α) : ℝ :=
  (pairCount (B x) (B y) q:ℝ)

lemma coarseKernel_symm (B : α → Finset H) (q : H) (x y : α) :
    coarseKernel B q x y=coarseKernel B q y x := by unfold coarseKernel; rw [pairCount_comm]

lemma coarseKernel_nonneg (B : α → Finset H) (q : H) (x y : α) :
    0≤coarseKernel B q x y := Nat.cast_nonneg _

lemma assembly_root_error (h : ℕ) (a : ZMod p) (P : Fin h → Finset (ZMod p×ZMod p))
    (hP : Pairwise (fun i j ↦ Disjoint (P i) (P j)))
    (hL : ∀ z : ZMod p×ZMod p, (∑ i : Fin h, ∑ j : Fin h,
      |(pairCount (P i) (P j) z:ℝ)-pairCount (curve (a+(i.val:ZMod p))) (curve (a+(j.val:ZMod p))) z|)≤10*(h:ℝ)+8)
    (B : α → Finset H) (ω : Fin h → α) (q : H) (M : ℝ) (hM : 0≤M)
    (hB : ∀ x y, coarseKernel B q x y≤M) (t s : ZMod p) :
    |(pairCount (assembly P (fun i ↦ B (ω i))) (assembly P (fun i ↦ B (ω i))) ((t,s),q):ℝ)-
      labelRootCount h a (fun i j ↦ coarseKernel B q (ω i) (ω j)) t s| ≤ M*(10*(h:ℝ)+8) := by
  have he := assembly_error P (fun i ↦ curve (a+(i.val:ZMod p))) hP (fun i ↦ B (ω i))
    M (10*(h:ℝ)+8) hM (t,s) q (fun i j ↦ hB (ω i) (ω j)) (hL (t,s))
  simp_rw [curve_pairCount] at he
  exact he

noncomputable def coarseBudget (h : ℕ) (B : α → Finset H) (S : Finset H) (w : H → ℝ) : ℝ :=
  ∑ q∈S, w q*(16*(h:ℝ)^2*colorVariance (coarseKernel B q)+
    4*(h:ℝ)*diagonalCenteredSecond (coarseKernel B q))

/-- One translate and one disjoint palette are selected before all later
coarse sets. The later choice is solely a coloring of the fixed labels.
Coarse sets need not be disjoint. -/
theorem exists_actual_pattern_for_later_colors (hp : p≠2) (h : ℕ)
    (hh : h^2+4*h+2<p) :
    ∃ (a : ZMod p) (P : Fin h → Finset (ZMod p×ZMod p)),
      (∀ i<h, a+(i:ZMod p)≠0) ∧ (∀ q<2*h, 2*a+(q:ZMod p)≠0) ∧
      Pairwise (fun i j ↦ Disjoint (P i) (P j)) ∧
      ∀ (B : α → Finset H) (S : Finset H) (M : H → ℝ),
        (∀ q∈S, 0≤M q) → (∀ q∈S, ∀ x y, coarseKernel B q x y≤M q) →
        ∀ (w : H → ℝ), (∀ q∈S, 0≤w q) →
        ∃ ω : Fin h → α, ∀ q∈S, ∀ t s : ZMod p,
          w q*((pairCount (assembly P (fun i ↦ B (ω i))) (assembly P (fun i ↦ B (ω i))) ((t,s),q):ℝ)-
            (h:ℝ)^2*kernelMean (coarseKernel B q))^2 ≤
          2*w q*(M q*(10*(h:ℝ)+8))^2+
            12*(h:ℝ)*(8*w q*(kernelMean (coarseKernel B q))^2*(h:ℝ)^2+coarseBudget h B S w) := by
  obtain ⟨a,ha,hop,hroot⟩ := exists_pattern_for_later_kernels (α := α) (κ := H) hp h (by omega)
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
  refine ⟨a,P,ha,hop,hP,fun B S M hM hB w hw ↦ ?_⟩
  obtain ⟨ω,hω⟩ := hroot S (coarseKernel B) (fun q hq ↦ coarseKernel_symm B q) w hw
  refine ⟨ω,fun q hq t s ↦ ?_⟩
  have hfirst := assembly_root_error h a P hP hL B ω q (M q) (hM q hq) (hB q hq) t s
  have hfirstSq :
      ((pairCount (assembly P (fun i ↦ B (ω i))) (assembly P (fun i ↦ B (ω i))) ((t,s),q):ℝ)-
        labelRootCount h a (fun i j ↦ coarseKernel B q (ω i) (ω j)) t s)^2 ≤
      (M q*(10*(h:ℝ)+8))^2 := by
    have he := mul_self_le_mul_self (abs_nonneg _) hfirst
    simpa only [←pow_two,sq_abs] using he
  have hweighted := mul_le_mul_of_nonneg_left hfirstSq (hw q hq)
  have hsecond := hω q hq t s
  change _ ≤ 6*(h:ℝ)*(8*w q*(kernelMean (coarseKernel B q))^2*(h:ℝ)^2+coarseBudget h B S w) at hsecond
  have hsq (x y z : ℝ) : (x-z)^2≤2*(x-y)^2+2*(y-z)^2 := by nlinarith [sq_nonneg (x-2*y+z)]
  have htotal := mul_le_mul_of_nonneg_left (hsq
    (pairCount (assembly P (fun i ↦ B (ω i))) (assembly P (fun i ↦ B (ω i))) ((t,s),q):ℝ)
    (labelRootCount h a (fun i j ↦ coarseKernel B q (ω i) (ω j)) t s)
    ((h:ℝ)^2*kernelMean (coarseKernel B q))) (hw q hq)
  nlinarith only [hweighted,hsecond,htotal]

end Erdos66ActualColorRootTransfer
