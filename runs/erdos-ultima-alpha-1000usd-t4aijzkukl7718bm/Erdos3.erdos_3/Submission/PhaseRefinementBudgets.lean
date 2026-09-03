import Submission.UnconditionalBiasedPhaseRefinement

/-! Explicit radius and error budgets for the local phase refinement.
The radius lower bound is a product of four stability denominators, not an
unspecified positive radius. -/
namespace Erdos3PhaseRefinementBudgets
open Finset Erdos3UnconditionalBiasedPhaseRefinement Erdos3BiasedQuadraticBohrRefinement
  Erdos3FiniteBohr Erdos3RelativeStableBohr
open scoped BigOperators Classical
set_option maxHeartbeats 5000000

variable {G : Type*} [AddCommGroup G] [Fintype G]

noncomputable def baseRadiusLower (d : ℕ) (R : ℝ) (o v z : ℕ) : ℝ :=
  R/(128*(windowDenominator d o : ℝ)*windowDenominator d v*windowDenominator d z)

noncomputable def stepRadiusLower (d : ℕ) (R σ β : ℝ) (o v z w : ℕ) : ℝ :=
  min (R/(512*(windowDenominator d o : ℝ)*windowDenominator d v*
    windowDenominator d z*windowDenominator d w)) (σ*β/16)

lemma baseRadiusLower_pos (d : ℕ) {R : ℝ} (hR : 0 < R) {o v z : ℕ}
    (ho : 0 < o) (hv : 0 < v) (hz : 0 < z) : 0 < baseRadiusLower d R o v z := by
  have ho' : (0 : ℝ) < windowDenominator d o := by exact_mod_cast windowDenominator_pos d ho
  have hv' : (0 : ℝ) < windowDenominator d v := by exact_mod_cast windowDenominator_pos d hv
  have hz' : (0 : ℝ) < windowDenominator d z := by exact_mod_cast windowDenominator_pos d hz
  unfold baseRadiusLower
  positivity

lemma stepRadiusLower_pos (d : ℕ) {R σ β : ℝ} (hR : 0 < R) (hσ : 0 < σ) (hβ : 0 < β)
    {o v z w : ℕ} (ho : 0 < o) (hv : 0 < v) (hz : 0 < z) (hw : 0 < w) :
    0 < stepRadiusLower d R σ β o v z w := by
  have ho' : (0 : ℝ) < windowDenominator d o := by exact_mod_cast windowDenominator_pos d ho
  have hv' : (0 : ℝ) < windowDenominator d v := by exact_mod_cast windowDenominator_pos d hv
  have hz' : (0 : ℝ) < windowDenominator d z := by exact_mod_cast windowDenominator_pos d hz
  have hw' : (0 : ℝ) < windowDenominator d w := by exact_mod_cast windowDenominator_pos d hw
  unfold stepRadiusLower
  positivity

lemma geometry_base_lower (D : Finset (AddChar G ℂ)) {R u r s : ℝ} {o v z w : ℕ}
    (hg : RefinementGeometry D R o v z w u r s) : baseRadiusLower D.card R o v z ≤ s := by
  calc
    _ = (((relativeWidth D o R/8)/(windowDenominator D.card v : ℝ)/4)/
        (windowDenominator D.card z : ℝ)/4) := by unfold baseRadiusLower relativeWidth; ring
    _ ≤ ((u/(windowDenominator D.card v : ℝ)/4)/(windowDenominator D.card z : ℝ)/4) := by
      gcongr
      exact hg.u_lower
    _ ≤ r/(windowDenominator D.card z : ℝ)/4 := by
      gcongr
      exact hg.r_lower
    _ ≤ s := hg.s_lower

lemma geometry_step_lower (D : Finset (AddChar G ℂ)) {R u r s σ β : ℝ} {o v z w : ℕ}
    (hg : RefinementGeometry D R o v z w u r s) :
    stepRadiusLower D.card R σ β o v z w ≤ min (relativeWidth D w s/4) (σ*β/16) := by
  apply min_le_min_right
  calc
    _ = baseRadiusLower D.card R o v z/(windowDenominator D.card w : ℝ)/4 := by
      unfold baseRadiusLower
      ring
    _ ≤ s/(windowDenominator D.card w : ℝ)/4 := by
      gcongr
      exact geometry_base_lower D hg
    _ = _ := rfl

lemma geometry_step_admissible (D : Finset (AddChar G ℂ))
    {R u r s σ β : ℝ} (hR : 0 < R) (hσ : 0 < σ) (hβ : 0 < β)
    {o v z w : ℕ} (ho : 0 < o) (hv : 0 < v) (hz : 0 < z) (hw : 0 < w)
    (hg : RefinementGeometry D R o v z w u r s) :
    let t := min (relativeWidth D w s/4) (σ*β/16)
    0 < s ∧ 0 < t ∧ t ≤ r ∧ t ≤ relativeWidth D z r ∧
      t ≤ relativeWidth D w s ∧ r+s+t ≤ relativeWidth D o R := by
  dsimp only
  have hU := relativeWidth_pos D ho hR
  have hu : 0 < u := (show 0 < relativeWidth D o R/8 by positivity).trans_le hg.u_lower
  have hvu := relativeWidth_pos D hv hu
  have hr : 0 < r := (show 0 < relativeWidth D v u/4 by positivity).trans_le hg.r_lower
  have hzr := relativeWidth_pos D hz hr
  have hs : 0 < s := (show 0 < relativeWidth D z r/4 by positivity).trans_le hg.s_lower
  have hws := relativeWidth_pos D hw hs
  have ht : 0 < min (relativeWidth D w s/4) (σ*β/16) := by positivity
  have htw := min_le_left (relativeWidth D w s/4) (σ*β/16)
  have hwq := relativeWidth_le_quarter D hw hs.le
  have hzq := relativeWidth_le_quarter D hz hr.le
  have hvq := relativeWidth_le_quarter D hv hu.le
  have hur := hg.u_upper
  have hrr := hg.r_upper
  have hsr := hg.s_upper
  refine ⟨hs,ht,?_,?_,?_,?_⟩ <;> linarith

/-- Simple numerical budgets imply the hypotheses and errors needed by the
refinement, with eta=beta/4 and spectral tolerance epsilon=beta^2/32. -/
lemma refinement_budget_bounds {β σ ρ : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1)
    (hσ : 0 < σ) (hσ1 : σ ≤ 1) {o v z w : ℕ}
    (ho : 0 < o) (hv : 0 < v) (hz : 0 < z) (hw : 0 < w) (hρ : 0 < ρ)
    (hoB : 1/(o : ℝ) ≤ β/8) (hvB : 1/((v : ℝ)*ρ) ≤ σ*β/16)
    (hzB : 1/(z : ℝ) ≤ σ*β^3/512) (hwB : 1/(w : ℝ) ≤ σ*β/16) :
    1/(z : ℝ) < β-2/(o : ℝ) ∧
    β/4 ≤ β-2/(o : ℝ)-1/((v : ℝ)*ρ)-1/(z : ℝ) ∧
    ∀ t : ℝ, t ≤ σ*β/16 →
      refinementError (1/((v : ℝ)*ρ)) (β-2/(o : ℝ)) (β^2/32) z w t ≤ σ/2 ∧
      1/((v : ℝ)*ρ)+1/(z : ℝ)/(β^2/32)+t+
        refinementError (1/((v : ℝ)*ρ)) (β-2/(o : ℝ)) (β^2/32) z w t ≤ σ := by
  have heps : 0 < β^2/32 := by positivity
  have hsig : σ*β ≤ β := by nlinarith
  have hb3 : β^3 ≤ β := by
    have hh : β^2 ≤ 1 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hh hβ.le]
  have hsb3 : σ*β^3 ≤ β := by nlinarith [mul_le_mul_of_nonneg_right hσ1 (pow_nonneg hβ.le 3)]
  have hzsmall : 1/(z : ℝ) ≤ β/8 := by linarith
  have h2 : 2/(o : ℝ) = 2*(1/(o : ℝ)) := by ring
  have ha : 1/((v : ℝ)*ρ) ≤ β/16 := by linarith
  have hden : β/2 ≤ β-2/(o : ℝ)-1/(z : ℝ) := by rw [h2]; linarith
  have hdenpos : 0 < β-2/(o : ℝ)-1/(z : ℝ) := (show 0 < β/2 by positivity).trans_le hden
  have hzdiv : 1/(z : ℝ)/(β^2/32) ≤ σ*β/16 := by
    apply (div_le_iff₀ heps).mpr
    convert hzB using 1 <;> ring
  refine ⟨by linarith,by linarith,?_⟩
  intro t ht
  have hflat : refinementError (1/((v : ℝ)*ρ)) (β-2/(o : ℝ)) (β^2/32) z w t ≤ σ/2 := by
    unfold refinementError
    apply (div_le_iff₀ hdenpos).mpr
    have hh := mul_le_mul_of_nonneg_left hden (show 0 ≤ σ/2 by positivity)
    nlinarith
  refine ⟨hflat,?_⟩
  have hσβ : σ*β ≤ σ := by nlinarith
  linarith

#print axioms geometry_step_lower
#print axioms refinement_budget_bounds
end Erdos3PhaseRefinementBudgets
