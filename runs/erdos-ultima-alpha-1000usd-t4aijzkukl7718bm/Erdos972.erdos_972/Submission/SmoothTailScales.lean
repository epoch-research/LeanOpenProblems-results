import Submission.SmoothDivisorTail
import Submission.SmoothCorrelationScale

/-! Two different smoothing regimes. The explicit tail estimate decays
at a slowly vanishing parameter, but its normalized budget diverges at
the much smaller parameter used in the verified Mangoldt comparison.
This concerns the particular upper bound, not the actual tail itself. -/
namespace Erdos972SmoothTailScales

open Filter
open scoped Topology
open Erdos972SmoothDivisorTail Erdos972SmoothCorrelationScale
open Erdos972PrimePowerError Erdos972PolynomialRowScales Erdos972ExponentialSum

noncomputable def slowParameter (u : ℕ) : ℝ := 1/Real.sqrt (1+Real.log u)

lemma slowParameter_pos (u : ℕ) : 0 < slowParameter u := by
  unfold slowParameter
  positivity [Real.log_natCast_nonneg u]

lemma sqrt_log_tendsto :
    Tendsto (fun u : ℕ => Real.sqrt (1+Real.log u)) atTop atTop := by
  apply Real.tendsto_sqrt_atTop.comp
  apply tendsto_atTop_mono (fun u : ℕ => show Real.log u ≤ 1+Real.log u by linarith)
  exact Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

lemma slow_damping_bound {u : ℕ} (hu : 0 < u) :
    damping (slowParameter u) (root64 u) ≤
      Real.exp 1 * Real.exp (-(1/65:ℝ)*Real.sqrt (1+Real.log u)) := by
  let x := Real.sqrt (1+Real.log u)
  have hx1 : 1 ≤ x := Real.one_le_sqrt.mpr (by linarith [Real.log_natCast_nonneg u])
  have hx0 : 0 < x := by linarith
  have hxsq : x^2 = 1+Real.log u := Real.sq_sqrt (by positivity [Real.log_natCast_nonneg u])
  have hroot := root64_log_bound hu
  have harg : -(1/x)*Real.log (root64 u) ≤ 1-(1/65:ℝ)*x := by
    have hh : -Real.log (root64 u) ≤ (1-(1/65:ℝ)*x)*x := by nlinarith only [hroot, hxsq, hx1]
    have he : -(1/x)*Real.log (root64 u) = (-Real.log (root64 u))/x := by ring
    rw [he]
    exact (div_le_iff₀ hx0).mpr hh
  calc
    _ ≤ Real.exp (1-(1/65:ℝ)*x) := Real.exp_le_exp.mpr harg
    _ = _ := by rw [sub_eq_add_neg, Real.exp_add]; congr 2; ring

/-- The finite-tail estimate does work at t_u=1/sqrt(1+log u), even after
normalization by t_u^2 and any fixed logarithmic loss. -/
theorem slow_damping_weight_tendsto (k : ℕ) :
    Tendsto (fun u : ℕ => damping (slowParameter u) (root64 u) *
      (1+Real.log u)^k/(slowParameter u)^2) atTop (𝓝 0) := by
  have hx := sqrt_log_tendsto
  have hlim := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
    ((2*k+2:ℕ):ℝ) (1/65) (by norm_num)).comp hx
  simp only [Real.rpow_natCast] at hlim
  have hlim' := hlim.const_mul (Real.exp 1)
  simp only [mul_zero] at hlim'
  apply squeeze_zero_norm' _ hlim'
  filter_upwards [eventually_ge_atTop (1:ℕ)] with u hu
  let x := Real.sqrt (1+Real.log u)
  have hx0 : 0 < x := Real.sqrt_pos.mpr (by positivity [Real.log_natCast_nonneg u])
  have hxsq : x^2 = 1+Real.log u := Real.sq_sqrt (by positivity [Real.log_natCast_nonneg u])
  have he : damping (slowParameter u) (root64 u)*(1+Real.log u)^k/(slowParameter u)^2 =
      damping (slowParameter u) (root64 u)*x^(2*k+2) := by
    change damping (slowParameter u) (root64 u)*(1+Real.log u)^k/(1/x)^2 = _
    rw [← hxsq, pow_add, pow_mul]
    field_simp
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity [damping_pos (slowParameter u) (root64 u)]), he]
  have hh := mul_le_mul_of_nonneg_right (slow_damping_bound hu) (pow_nonneg hx0.le (2*k+2))
  exact hh.trans_eq (by dsimp [x]; ring)

/-- At the smaller comparison parameter, every cutoff D<=N has damping
approaching one. This does not assert that its actual signed tail is large. -/
theorem comparison_damping_tendsto_one {α : ℝ} (hα : 1 ≤ α) (D : ℕ → ℕ)
    (hD : ∀ᶠ N : ℕ in atTop, D N ≤ N) :
    Tendsto (fun N => damping (smoothingParameter α N) (D N)) atTop (𝓝 1) := by
  have hlow := polynomial_cutoff_damping_tendsto_one hα (1:ℝ)
  simp only [neg_mul, one_mul] at hlow
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds
  · filter_upwards [hD] with N hDN
    apply Real.exp_le_exp.mpr
    simpa only [neg_mul] using mul_le_mul_of_nonpos_left (monotone_log_natCast hDN)
      (neg_nonpos.mpr (smoothingParameter_pos α N).le)
  · filter_upwards [] with N
    apply Real.exp_le_one_iff.mpr
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (smoothingParameter_pos α N).le)
      (Real.log_natCast_nonneg _)

lemma comparison_inverse_square_tendsto {α : ℝ} (hα : 1 ≤ α) :
    Tendsto (fun N : ℕ => 1/(smoothingParameter α N)^2) atTop atTop := by
  have hlog : Tendsto (fun N : ℕ => 1+Real.log N) atTop atTop := by
    apply tendsto_atTop_mono (fun N : ℕ => show Real.log N ≤ 1+Real.log N by linarith)
    exact Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hb : Tendsto (fun N : ℕ => 1+Real.log (floorMul α N)) atTop atTop := by
    apply tendsto_atTop_mono (fun N : ℕ => show 1+Real.log N ≤ 1+Real.log (floorMul α N) by
      have hh := monotone_log_natCast (self_le_floorMul hα N)
      linarith only [hh]) hlog
  have hh := (tendsto_pow_atTop (by decide : (10:ℕ) ≠ 0)).comp hb
  convert hh using 1
  funext N
  unfold smoothingParameter
  simp only [one_div, inv_pow, inv_inv, ← pow_mul, Function.comp_apply, show 5*2 = (10:ℕ) by decide]

/-- The particular normalized upper budget diverges at the comparison
parameter. This is NOT a lower bound for the actual correlation error. -/
theorem comparison_tail_budget_tendsto_atTop {α : ℝ} (hα : 1 ≤ α) (D : ℕ → ℕ)
    (hD : ∀ᶠ N : ℕ in atTop, D N ≤ N) :
    Tendsto (fun N : ℕ => divisorTailBudget (smoothingParameter α N) α (D N) N /
      ((smoothingParameter α N)^2 * N)) atTop atTop := by
  have hh := (comparison_damping_tendsto_one hα D hD).pos_mul_atTop (by norm_num : (0:ℝ) < 1)
    (comparison_inverse_square_tendsto hα)
  apply tendsto_atTop_mono' atTop _ hh
  filter_upwards [eventually_ge_atTop (1:ℕ)] with N hN
  let t := smoothingParameter α N
  let ρ := damping t (D N)
  let M := floorMul α N
  let L := 1+Real.log M
  have ht : 0 < t := smoothingParameter_pos α N
  have hρ : 0 < ρ := damping_pos t (D N)
  have hNR : (0:ℝ) < N := Nat.cast_pos.mpr hN
  have hL : 1 ≤ L := by dsimp [L]; linarith [Real.log_natCast_nonneg M]
  have hM : (0:ℝ) ≤ M := Nat.cast_nonneg _
  have hinner : ρ ≤ ρ*L+ρ^2/2*L^3 := by
    have hfirst := le_mul_of_one_le_right hρ.le hL
    have hsecond : 0 ≤ ρ^2/2*L^3 := by positivity
    linarith only [hfirst, hsecond]
  have hbudget : (N:ℝ)*ρ ≤ divisorTailBudget t α (D N) N := by
    change (N:ℝ)*ρ ≤ ((N:ℝ)+M)*(ρ*L+ρ^2/2*L^3)
    exact mul_le_mul (by linarith only [hM]) hinner hρ.le (by positivity)
  calc
    _ = ((N:ℝ)*ρ)/(t^2*N) := by change ρ*(1/t^2) = _; field_simp
    _ ≤ _ := div_le_div_of_nonneg_right hbudget (by positivity)

#print axioms slow_damping_weight_tendsto
#print axioms comparison_damping_tendsto_one
#print axioms comparison_tail_budget_tendsto_atTop

end Erdos972SmoothTailScales
