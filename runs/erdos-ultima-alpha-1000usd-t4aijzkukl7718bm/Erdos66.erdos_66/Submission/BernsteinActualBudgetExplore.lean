import Submission.BernsteinRootBudgetExplore
import Submission.LogarithmicActualBudgetExplore

/-! Actual finite-set transfer retaining the centered coarse variances,
range bounds, finite target logarithm, and origin-repair term. -/
namespace Erdos66BernsteinActualBudget
open Erdos66UniformSelection Erdos66UniformColorMoments Erdos66BernsteinColorEnergy
  Erdos66BernsteinRootBudget Erdos66OriginRepair Erdos66ParabolaRepair
  Erdos66CenteredColorSelection Erdos66LogarithmicActualBudget
  Erdos66DisjointPaletteAssembly Erdos66DisjointCurvePalette Erdos66ActualColorRootTransfer
open scoped Classical
set_option maxHeartbeats 3000000
variable {α : Type*} [Fintype α] [Nonempty α] [DecidableEq α]

variable {p : ℕ} [Fact p.Prime]
variable {H : Type*} [AddCommGroup H] [DecidableEq H]

/-- The field translate and disjoint palette precede the coarse data. The
later coloring handles every listed coarse target and ALL fine targets.
Origin repair is included, with a separate explicit error term. -/
theorem exists_actual_bernstein_budget (hp : p≠2) (h : ℕ) (hh : h^2+4*h+2<p) :
    ∃ (a : ZMod p) (P : Fin h → Finset (ZMod p×ZMod p)),
      (∀ i<h, a+(i:ZMod p)≠0) ∧ (∀ q<2*h, 2*a+(q:ZMod p)≠0) ∧
      Pairwise (fun i j ↦ Disjoint (P i) (P j)) ∧
      ∀ (B : α → Finset H) (S : Finset H) (M : H → ℝ),
        (∀ q∈S, 0<M q) → (∀ q∈S, ∀ x y, coarseKernel B q x y≤M q) →
        ∃ ω : Fin h → α, ∀ q∈S, ∀ t s : ZMod p,
          ((pairCount (assembly P (fun i ↦ B (ω i)))
            (assembly P (fun i ↦ B (ω i))) ((t,s),q):ℝ)-
              (h:ℝ)^2*kernelMean (coarseKernel B q))^2≤
            2*(M q*(10*(h:ℝ)+8))^2+
              12*(h:ℝ)*(8*(kernelMean (coarseKernel B q))^2*(h:ℝ)^2+
                2*bernsteinEnergy h (2*S.card) (colorVariance (coarseKernel B q)) (M q)) := by
  obtain ⟨a,ha,hop,hroot⟩ := exists_pattern_bernstein_root_budget (α := α) (κ := H)
    hp h (by omega)
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
  refine ⟨a,P,ha,hop,hP,fun B S M hM hB ↦ ?_⟩
  obtain ⟨ω,hω⟩ := hroot S (coarseKernel B) (fun q _ ↦ coarseKernel_symm B q)
    M hM (fun q hq ↦ centered_bound_of_nonnegative (coarseKernel B q) (M q)
      (coarseKernel_nonneg B q) (hB q hq))
  refine ⟨ω,fun q hq t s ↦ ?_⟩
  have hfirst := assembly_root_error h a P hP hL B ω q (M q) (hM q hq).le
    (hB q hq) t s
  have hfirstSq :
      ((pairCount (assembly P (fun i ↦ B (ω i))) (assembly P (fun i ↦ B (ω i))) ((t,s),q):ℝ)-
        Erdos66FiniteLabelRootTransfer.labelRootCount h a
          (fun i j ↦ coarseKernel B q (ω i) (ω j)) t s)^2≤(M q*(10*(h:ℝ)+8))^2 := by
    have he := mul_self_le_mul_self (abs_nonneg _) hfirst
    simpa only [←pow_two,sq_abs] using he
  have hsecond := hω q hq t s
  have hsq (x y z : ℝ) : (x-z)^2≤2*(x-y)^2+2*(y-z)^2 := by
    nlinarith [sq_nonneg (x-2*y+z)]
  have htotal := hsq
    (pairCount (assembly P (fun i ↦ B (ω i))) (assembly P (fun i ↦ B (ω i))) ((t,s),q):ℝ)
    (Erdos66FiniteLabelRootTransfer.labelRootCount h a
      (fun i j ↦ coarseKernel B q (ω i) (ω j)) t s)
    ((h:ℝ)^2*kernelMean (coarseKernel B q))
  nlinarith only [hfirstSq,hsecond,htotal]

end Erdos66BernsteinActualBudget
