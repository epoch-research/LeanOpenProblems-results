import Submission.GrowingRationalGrid

/-! Sublinear budgets for polynomially growing rational-frequency grids. -/
namespace Erdos972GrowingRationalGridBudgets

open Filter Finset ArithmeticFunction
open scoped Topology
open Erdos972GrowingRationalGrid Erdos972PolynomialRowScales
open Erdos972AsymmetricDiagonalBudget Erdos972PrimeRotation
open Erdos972ScaledPrimeRows Erdos972DualPrimeRows Erdos972GrowingTypeI
open Erdos972CovarianceScaleBudgets Erdos972CenteredRowScales
open Erdos972PrimePowerError Erdos972FloorCovarianceFourier

set_option maxHeartbeats 2000000
attribute [local irreducible] root64

lemma bandCutoff_powers {u : ℕ} (hu : 0 < u) :
    (bandCutoff u : ℝ)^5 ≤ (root64 u : ℝ)^2 ∧
      (bandCutoff u : ℝ)^6 ≤ (root64 u : ℝ)^2 := by
  obtain ⟨hB, hB4, _⟩ := bandCutoff_bounds hu
  have hB1 : (1 : ℝ) ≤ bandCutoff u := by exact_mod_cast hB
  have hB4R : (bandCutoff u : ℝ)^4 ≤ root64 u := by exact_mod_cast hB4
  have hB8 : (bandCutoff u : ℝ)^8 ≤ (root64 u : ℝ)^2 := by
    convert pow_le_pow_left₀ (by positivity) hB4R 2 using 1 <;> ring
  exact ⟨(pow_le_pow_right₀ hB1 (by norm_num)).trans hB8,
    (pow_le_pow_right₀ hB1 (by norm_num)).trans hB8⟩

lemma grid_prime_error_tendsto (K k : ℕ) :
    Tendsto (fun u : ℕ => (root64 u : ℝ)*(1+Real.log u)^k*
      ((bandCutoff u : ℝ)^5*scaledRowError K u (root64 u))/(u : ℝ)^6) atTop (𝓝 0) := by
  let C := 28+rotationConstant (256*K)
  have hC : 0 < C := by dsimp only [C]; positivity [rotationConstant_pos (256*K)]
  apply squeeze_zero_norm' _ (cutoff_log_div_tendsto C hC (k+5))
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with u hu
  have hu0 : (0 : ℝ) < u := Nat.cast_pos.mpr hu
  have hv : 0 < root64 u := (root64_bounds hu).1
  have hv0 : (0 : ℝ) < root64 u := Nat.cast_pos.mpr hv
  have hB0 : (0 : ℝ) < bandCutoff u := Nat.cast_pos.mpr (bandCutoff_bounds hu).1
  have hM : 0 < mobiusCutoff u := (root64_bounds hv).1
  have hM0 : (0 : ℝ) < mobiusCutoff u := Nat.cast_pos.mpr hM
  have hBM : (mobiusCutoff u : ℝ) ≤ bandCutoff u := Nat.cast_le.mpr (small_cutoff_le_bandCutoff hu)
  have hratio : (bandCutoff u : ℝ)^5/(root64 u : ℝ)^2 ≤ 1/(mobiusCutoff u : ℝ) := by
    apply le_trans (b := 1/(bandCutoff u : ℝ))
    · apply (div_le_div_iff₀ (sq_pos_of_pos hv0) hB0).mpr
      nlinarith only [(bandCutoff_powers hu).2]
    · exact one_div_le_one_div_of_le hM0 hBM
  rw [Real.norm_eq_abs, abs_of_nonneg (by
    unfold scaledRowError
    positivity [rotationConstant_pos (256*K), Real.log_natCast_nonneg u])]
  have he : (root64 u : ℝ)*(1+Real.log u)^k*
      ((bandCutoff u : ℝ)^5*scaledRowError K u (root64 u))/(u : ℝ)^6 =
        C*(1+Real.log u)^(k+5)*((bandCutoff u : ℝ)^5/(root64 u : ℝ)^2) := by
    unfold scaledRowError
    rw [pow_add]
    dsimp only [C]
    field_simp
  rw [he]
  have hh := mul_le_mul_of_nonneg_left hratio
    (show 0 ≤ C*(1+Real.log u)^(k+5) by positivity [Real.log_natCast_nonneg u])
  exact hh.trans_eq (by ring)

lemma fifth_family_divisor_error_tendsto (k : ℕ) :
    Tendsto (fun u : ℕ => (root64 u : ℝ)^5*(1+Real.log u)^k/(u : ℝ)^2) atTop (𝓝 0) := by
  have hh := root64_log_div_tendsto 1 (by norm_num) k
  simp only [one_mul] at hh
  apply squeeze_zero_norm' _ hh
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with u hu
  have hu0 : (0 : ℝ) < u := Nat.cast_pos.mpr hu
  obtain ⟨hv, hvu, _⟩ := root64_bounds hu
  have hv0 : (0 : ℝ) < root64 u := Nat.cast_pos.mpr hv
  have hv3 : (root64 u)^3 ≤ u := (Nat.pow_le_pow_right hv (by norm_num : 3 ≤ 64)).trans hvu
  have hv6 : (root64 u : ℝ)^6 ≤ (u : ℝ)^2 := by
    have hcast : (root64 u : ℝ)^3 ≤ u := by exact_mod_cast hv3
    convert pow_le_pow_left₀ (by positivity) hcast 2 using 1 <;> ring
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity [Real.log_natCast_nonneg u])]
  apply (div_le_div_iff₀ (sq_pos_of_pos hu0) hv0).mpr
  have hm := mul_le_mul_of_nonneg_right hv6
    (pow_nonneg (show 0 ≤ 1+Real.log u by positivity [Real.log_natCast_nonneg u]) k)
  nlinarith only [hm]

lemma grid_divisor_error_tendsto (k : ℕ) :
    Tendsto (fun u : ℕ => (root64 u : ℝ)*(1+Real.log u)^k*
      ((bandCutoff u : ℝ)^5*(root64 u : ℝ)*(236*(root64 u : ℝ)*(u : ℝ)^4+1))/(u : ℝ)^6)
      atTop (𝓝 0) := by
  have hh := (fifth_family_divisor_error_tendsto k).const_mul 237
  simp only [mul_zero] at hh
  apply squeeze_zero_norm' _ hh
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with u hu
  have hu0 : (0 : ℝ) < u := Nat.cast_pos.mpr hu
  have hu1 : (1 : ℝ) ≤ u := by exact_mod_cast hu
  have hv1 : (1 : ℝ) ≤ root64 u := by exact_mod_cast (root64_bounds hu).1
  have hcoef : 236*(root64 u : ℝ)*(u : ℝ)^4+1 ≤ 237*(root64 u : ℝ)*(u : ℝ)^4 := by
    have hh' := one_le_mul_of_one_le_of_one_le hv1 (one_le_pow₀ hu1 (n := 4))
    linarith only [hh']
  have hB5 := (bandCutoff_powers hu).1
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity [Real.log_natCast_nonneg u])]
  calc
    _ = (bandCutoff u : ℝ)^5*(root64 u : ℝ)^2*(1+Real.log u)^k*
        (236*(root64 u : ℝ)*(u : ℝ)^4+1)/(u : ℝ)^6 := by ring
    _ ≤ (root64 u : ℝ)^2*(root64 u : ℝ)^2*(1+Real.log u)^k*
        (237*(root64 u : ℝ)*(u : ℝ)^4)/(u : ℝ)^6 := by gcongr
    _ = _ := by field_simp

noncomputable def gridBudget (α : ℝ) (u : ℕ) : ℝ :=
  15*(1+4*Real.pi)*(bandCutoff u : ℝ)^5*(root64 u : ℝ)*
    (1+Real.log (α*scaleCutoff α u))^2*
      (scaledRowError (dualScaleLoss α) u (root64 u)+40*(root64 u : ℝ)*
        (1+Real.log (α*scaleCutoff α u))^2*(236*(root64 u : ℝ)*(u : ℝ)^4+1))

lemma gridBudget_tendsto {α : ℝ} (hα : 1 ≤ α) :
    Tendsto (fun u => gridBudget α u/(scaleCutoff α u : ℝ)) atTop (𝓝 0) := by
  let C := 15*(1+4*Real.pi)
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hp := scale_log_weight_tendsto hα 2 hC
    (fun u => (bandCutoff u : ℝ)^5*scaledRowError (dualScaleLoss α) u (root64 u))
    (by intro u; unfold scaledRowError; positivity [rotationConstant_pos (256*dualScaleLoss α), Real.log_natCast_nonneg u])
    (grid_prime_error_tendsto (dualScaleLoss α) 2)
  have hd := scale_log_weight_tendsto hα 4 (show 0 ≤ 40*C by positivity)
    (fun u => (bandCutoff u : ℝ)^5*(root64 u : ℝ)*(236*(root64 u : ℝ)*(u : ℝ)^4+1))
    (by intro u; positivity) (grid_divisor_error_tendsto 4)
  have hh := hp.add hd
  simp only [add_zero] at hh
  apply hh.congr
  intro u
  dsimp only [gridBudget, C]
  ring

lemma eventually_gridBudget_small {α : ℝ} (hα : 1 ≤ α) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ u : ℕ in atTop, gridBudget α u ≤ ε*(scaleCutoff α u : ℝ) :=
  eventually_bound_of_scaled_limit hα _ (gridBudget_tendsto hα) hε

/-- Even the enlarged collection occupies a vanishing fraction of the full
Fourier group; this is a coverage statement, not a cancellation estimate. -/
theorem rationalGrid_density_zero {α : ℝ} (hα : 1 ≤ α) :
    Tendsto (fun u => ((rationalGrid (floorMul α (scaleCutoff α u)+1) (bandCutoff u)).card : ℝ)/
      (floorMul α (scaleCutoff α u)+1 : ℕ)) atTop (𝓝 0) := by
  have hh := root64_log_div_tendsto 3 (by norm_num) 0
  simp only [pow_zero, mul_one] at hh
  apply squeeze_zero_norm' _ hh
  filter_upwards [eventually_ge_atTop (1 : ℕ), eventually_ge_atTop ⌈α⌉₊] with u hu huα
  have hu0 : (0 : ℝ) < u := Nat.cast_pos.mpr hu
  obtain ⟨hB, hB4, _⟩ := bandCutoff_bounds hu
  have hB3 : bandCutoff u^3 ≤ root64 u := (Nat.pow_le_pow_right hB (by norm_num : 3 ≤ 4)).trans hB4
  have hc : ((rationalGrid (floorMul α (scaleCutoff α u)+1) (bandCutoff u)).card : ℝ) ≤
      3*(root64 u : ℝ) := by
    have hi : ((rationalGrid (floorMul α (scaleCutoff α u)+1) (bandCutoff u)).card : ℝ) ≤
        (gridIndices (bandCutoff u)).card := by exact_mod_cast (card_image_le)
    have h3 : (bandCutoff u : ℝ)^3 ≤ root64 u := by exact_mod_cast hB3
    exact (hi.trans (gridIndices_card_real hB)).trans (mul_le_mul_of_nonneg_left h3 (by norm_num))
  have huN := (scaleCutoff_bounds hα hu ((Nat.le_ceil α).trans (Nat.cast_le.mpr huα))).1
  have hNM : scaleCutoff α u ≤ floorMul α (scaleCutoff α u) := self_le_floorMul hα _
  have huJ : (u : ℝ) ≤ (floorMul α (scaleCutoff α u)+1 : ℕ) := by
    exact_mod_cast (huN.trans hNM).trans (Nat.le_succ _)
  obtain ⟨hv, hv64, _⟩ := root64_bounds hu
  have hv0 : (0 : ℝ) < root64 u := Nat.cast_pos.mpr hv
  have hv2 : (root64 u : ℝ)^2 ≤ u := by
    exact_mod_cast (Nat.pow_le_pow_right hv (by norm_num : 2 ≤ 64)).trans hv64
  have hJ : (0 : ℝ) < (floorMul α (scaleCutoff α u)+1 : ℕ) := by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  apply (div_le_div_iff₀ hJ hv0).mpr
  have hc' := mul_le_mul_of_nonneg_right hc hv0.le
  nlinarith only [hc', hv2, huJ]

#print axioms gridBudget_tendsto
#print axioms rationalGrid_density_zero
end Erdos972GrowingRationalGridBudgets
