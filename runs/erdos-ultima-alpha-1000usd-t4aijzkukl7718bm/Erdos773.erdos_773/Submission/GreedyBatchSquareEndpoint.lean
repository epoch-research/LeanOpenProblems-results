import Submission.GreedyBatchSquareScales
import Submission.UniformSquareSampling

/-! The coefficient-one two-thirds endpoint for Sidon subsets of squares.
This does not establish any exponent greater than two thirds. -/
namespace Erdos773.GreedyBatchSquareEndpoint
open Finset Filter SquareCollisionCodegrees HypergraphDegreeTrim
open GreedyBatchSquareScales GreedyBatchVolume
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096
set_option exponentiation.threshold 2048
noncomputable section

/-- An actual unit-coefficient endpoint, with all finite hypotheses supplied.
The near-linear conjecture remains a strictly stronger statement. -/
theorem eventual_endpoint : ∀ᶠ N : ℕ in atTop,
    (N:ℝ)^(2/3:ℝ)≤(maxSidonSubsetCard ((Icc 1 N).image (fun n : ℕ => n^2)):ℝ) := by
  classical
  let M : ℕ := max 100000000000 (max 2000000 (3*increment (exponent+increment exponent)))
  have hpow : Tendsto (fun N : ℕ => (N:ℝ)^eta) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num [eta])).comp tendsto_natCast_atTop_atTop
  have hlog : Tendsto (fun N : ℕ => Real.log (N:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hsmall := ((isLittleO_log_rpow_atTop (by norm_num : (0:ℝ)<1/160000)).comp_tendsto
    (tendsto_natCast_atTop_atTop : Tendsto (fun N : ℕ => (N:ℝ)) atTop atTop)).bound
      (by norm_num : (0:ℝ)<1/2)
  have hbudget := ((isLittleO_log_rpow_atTop (by norm_num [eta] : (0:ℝ)<eta)).comp_tendsto
    (tendsto_natCast_atTop_atTop : Tendsto (fun N : ℕ => (N:ℝ)) atTop atTop)).bound
      (by norm_num : (0:ℝ)<1/16)
  filter_upwards [hpow.eventually_ge_atTop (M:ℝ),hlog.eventually_ge_atTop 4000000000000000000,
    hsmall,hbudget,eventually_ge_atTop 1,
    UniformSquareSampling.logarithmic_sampling (1/100000) (by norm_num) (by norm_num),
    eventually_pair_codegree_bound eta (by norm_num [eta])]
    with N hM hL hs hb hN hsample hpair
  have hX0 : (0:ℝ)<N := by exact_mod_cast hN
  have hX1 : (1:ℝ)≤N := by exact_mod_cast hN
  have hL0 : 0<Real.log (N:ℝ) := by linarith only [hL]
  have hL1 : 1≤Real.log (N:ℝ) := by linarith only [hL]
  have hmM : M≤root (N:ℝ) := by exact_mod_cast hM.trans (root_lower (N:ℝ))
  have hmEff : 100000000000≤root (N:ℝ) := (le_max_left _ _).trans hmM
  have hm : 2000000≤root (N:ℝ) := (le_max_left _ _).trans ((le_max_right _ _).trans hmM)
  have hmV : 3*increment (exponent+increment exponent)≤root (N:ℝ) :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hmM)
  have hM2 : (2:ℝ)≤M := by exact_mod_cast (show 2≤M from (by omega : 2≤100000000000).trans (le_max_left _ _))
  have htwo : (2:ℝ)≤(N:ℝ)^eta := hM2.trans hM
  have hs' : Real.log (N:ℝ)≤(1/2:ℝ)*(N:ℝ)^(1/160000:ℝ) := by
    simpa only [Function.comp_apply,Real.norm_eq_abs,abs_of_nonneg hL0.le,
      abs_of_nonneg (Real.rpow_nonneg hX0.le _)] using hs
  have hb' : Real.log (N:ℝ)≤(1/16:ℝ)*(N:ℝ)^eta := by
    simpa only [Function.comp_apply,Real.norm_eq_abs,abs_of_nonneg hL0.le,
      abs_of_nonneg (Real.rpow_nonneg hX0.le _)] using hb
  have hT3 : (horizon (N:ℝ))^3≤(root (N:ℝ):ℝ)/16 := by
    rw [horizon_cube hL0.le]
    calc
      _ ≤ Real.log (N:ℝ) := by dsimp [c]; linarith only [hL0.le]
      _ ≤ (1/16:ℝ)*(N:ℝ)^eta := hb'
      _ ≤ _ := by have := root_lower (N:ℝ); linarith only [this]
  have hdU : scale (N:ℝ)≤(root (N:ℝ):ℝ)^exponent :=
    (scale_upper hX1 hL1).trans (volume hX0.le)
  have hvol : N≤root (N:ℝ)^exponent := by exact_mod_cast volume hX0.le
  obtain ⟨A,hA,hAP,hdegree,hcard⟩ := hsample
  have hdegree' (x : ℕ) (hx : x∈A) : (degree (edges A) x:ℝ)≤(scale (N:ℝ))^3 := by
    rw [scale_cube hX0.le]
    exact (hdegree x (hA hx)).le
  have hpair' : ∀ x∈A, ∀ y∈A, x≠y → (pairEdges A x y).card≤root (N:ℝ) := by
    intro x hx y hy hxy
    have hmono : ((pairEdges A x y).card:ℝ)≤(pairEdges (Icc 1 N) x y).card := by
      exact_mod_cast card_le_card (pairEdges_mono hA x y)
    exact_mod_cast (hmono.trans (hpair x (hA hx) y (hA hy) hxy)).trans (root_lower (N:ℝ))
  have hcert := GreedyBatchSquareCertificate.certificate N (root (N:ℝ)) exponent
    (scale (N:ℝ)) (horizon (N:ℝ)) (root (N:ℝ)) A hm hmV (scale_pos hX0 hL0) hdU
    (by omega) le_rfl (by have := horizon_large hL; linarith only [this]) hT3
    (terminal hX1 hm hL htwo hs') hA hvol hAP hdegree' hpair'
  have hcard' : loss*(N:ℝ)/Real.log N≤(A.card:ℝ) := by
    norm_num [loss] at hcard ⊢
    exact hcard
  exact (coefficient hX0 hL hmEff hcard').trans hcert

#print axioms eventual_endpoint
end
end Erdos773.GreedyBatchSquareEndpoint
