import FormalConjectures.Util.ProblemImports
import Submission.Zeta341
import Submission.ZeroFree

/-!
The regularized zeta `(s-1) ζ(s)` (value 1 at `s = 1`) is entire.
-/

open Complex Filter Metric Set
open scoped Topology

noncomputable section

/-- Regularized zeta: `(s-1) ζ(s)` with value `1` at the removable singularity `s = 1`. -/
def zetaReg (s : ℂ) : ℂ := if s = 1 then 1 else (s - 1) * riemannZeta s

lemma zetaReg_apply_of_ne {s : ℂ} (hs : s ≠ 1) :
    zetaReg s = (s - 1) * riemannZeta s :=
  if_neg hs

lemma zetaReg_one : zetaReg 1 = 1 := if_pos rfl

lemma zetaReg_eqOn_mul : EqOn zetaReg (fun s => (s - 1) * riemannZeta s) ({1}ᶜ) := by
  intro s hs
  exact zetaReg_apply_of_ne (mem_compl_singleton_iff.mp hs)

lemma tendsto_zetaReg_punctured : Tendsto zetaReg (𝓝[≠] 1) (𝓝 1) := by
  refine riemannZeta_residue_one.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact (zetaReg_apply_of_ne (mem_compl_singleton_iff.mp hs)).symm

lemma tendsto_zetaReg_one : Tendsto zetaReg (𝓝 1) (𝓝 1) := by
  have hpure : Tendsto zetaReg (pure 1) (𝓝 1) := by
    simpa [zetaReg_one] using tendsto_pure_nhds zetaReg (1 : ℂ)
  have h : Tendsto zetaReg (𝓝[≠] 1 ⊔ pure 1) (𝓝 1) :=
    tendsto_sup.mpr ⟨tendsto_zetaReg_punctured, hpure⟩
  rwa [nhdsNE_sup_pure] at h

lemma continuousAt_zetaReg_one : ContinuousAt zetaReg 1 := by
  change Tendsto zetaReg (𝓝 1) (𝓝 (zetaReg 1))
  simpa [zetaReg_one] using tendsto_zetaReg_one

lemma differentiableAt_zetaReg_of_ne {s : ℂ} (hs : s ≠ 1) :
    DifferentiableAt ℂ zetaReg s := by
  have hζ : DifferentiableAt ℂ riemannZeta s := differentiableAt_riemannZeta hs
  have hmul : DifferentiableAt ℂ (fun w => (w - 1) * riemannZeta w) s :=
    (differentiableAt_id.sub (differentiableAt_const 1)).mul hζ
  have heq : zetaReg =ᶠ[𝓝 s] fun w => (w - 1) * riemannZeta w := by
    refine Filter.eventuallyEq_iff_exists_mem.mpr ?_
    exact ⟨{1}ᶜ, isOpen_compl_singleton.mem_nhds hs, zetaReg_eqOn_mul⟩
  exact hmul.congr_of_eventuallyEq heq

lemma eventually_differentiableAt_zetaReg_punctured :
    ∀ᶠ z in 𝓝[≠] (1 : ℂ), DifferentiableAt ℂ zetaReg z := by
  filter_upwards [self_mem_nhdsWithin] with z hz
  exact differentiableAt_zetaReg_of_ne (mem_compl_singleton_iff.mp hz)

lemma analyticAt_zetaReg_one : AnalyticAt ℂ zetaReg 1 :=
  analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
    eventually_differentiableAt_zetaReg_punctured continuousAt_zetaReg_one

lemma differentiable_zetaReg : Differentiable ℂ zetaReg := by
  intro s
  by_cases hs : s = 1
  · subst hs
    exact analyticAt_zetaReg_one.differentiableAt
  · exact differentiableAt_zetaReg_of_ne hs

lemma riemannZeta_eq_zetaReg_div {s : ℂ} (hs : s ≠ 1) :
    riemannZeta s = zetaReg s / (s - 1) := by
  rw [zetaReg_apply_of_ne hs, mul_comm, mul_div_cancel_right₀]
  exact sub_ne_zero.mpr hs

lemma zetaReg_ne_zero_of_zeta {s : ℂ} (hs : s ≠ 1) (hz : riemannZeta s ≠ 0) :
    zetaReg s ≠ 0 := by
  rw [zetaReg_apply_of_ne hs]
  exact mul_ne_zero (sub_ne_zero.mpr hs) hz

open ArithmeticFunction hiding log

lemma deriv_riemannZeta_div_eq_neg_LSeries {s : ℂ} (hs : 1 < s.re) :
    deriv riemannZeta s / riemannZeta s =
      - LSeries (fun n => (vonMangoldt n : ℂ)) s := by
  have h := LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs
  -- h : L Λ s = - deriv ζ s / ζ s
  rw [h]
  ring

lemma zetaReg_hasDerivAt_of_ne {s : ℂ} (hs : s ≠ 1) :
    HasDerivAt zetaReg ((riemannZeta s) + (s - 1) * deriv riemannZeta s) s := by
  have hζ : DifferentiableAt ℂ riemannZeta s := differentiableAt_riemannZeta hs
  have heq : zetaReg =ᶠ[𝓝 s] fun w => (w - 1) * riemannZeta w := by
    refine Filter.eventuallyEq_iff_exists_mem.mpr ?_
    exact ⟨{1}ᶜ, isOpen_compl_singleton.mem_nhds hs, zetaReg_eqOn_mul⟩
  have hmul : HasDerivAt (fun w => (w - 1) * riemannZeta w)
      (riemannZeta s + (s - 1) * deriv riemannZeta s) s := by
    have hid : HasDerivAt (fun w : ℂ => w - 1) 1 s :=
      (hasDerivAt_id s).sub_const 1
    have hζd : HasDerivAt riemannZeta (deriv riemannZeta s) s := hζ.hasDerivAt
    convert hid.mul hζd using 1
    simp [one_mul]
  exact hmul.congr_of_eventuallyEq heq

lemma deriv_zetaReg_of_ne {s : ℂ} (hs : s ≠ 1) :
    deriv zetaReg s = riemannZeta s + (s - 1) * deriv riemannZeta s :=
  (zetaReg_hasDerivAt_of_ne hs).deriv

/-- Logarithmic derivative of `zetaReg` away from `s = 1` and the zeros of `ζ`. -/
lemma logDeriv_zetaReg {s : ℂ} (hs : s ≠ 1) (hz : riemannZeta s ≠ 0) :
    deriv zetaReg s / zetaReg s =
      1 / (s - 1) + deriv riemannZeta s / riemannZeta s := by
  rw [deriv_zetaReg_of_ne hs, zetaReg_apply_of_ne hs]
  have h1 : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  field [h1, hz]

lemma logDeriv_zetaReg_eq_neg_LSeries {s : ℂ} (hs : 1 < s.re) :
    deriv zetaReg s / zetaReg s =
      1 / (s - 1) - LSeries (fun n => (vonMangoldt n : ℂ)) s := by
  have hs1 : s ≠ 1 := by
    intro h
    have : (1 : ℝ) < 1 := by simpa [h] using hs
    linarith
  have hz : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_le_re (le_of_lt hs)
  rw [logDeriv_zetaReg hs1 hz, deriv_riemannZeta_div_eq_neg_LSeries hs]
  ring

end
