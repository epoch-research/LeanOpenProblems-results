import Submission.VaughanDiagonalBound
import Submission.CommonCovarianceScales

/-! Unequal Vaughan cutoffs and an explicit vanishing budget for the
multiplicative diagonal. No off-diagonal signed estimate is asserted. -/
namespace Erdos972AsymmetricDiagonalBudget

open Filter
open scoped Topology
open Erdos972PolynomialRowScales Erdos972GrowingTypeI
open Erdos972VaughanDiagonalBound Erdos972CovarianceScaleBudgets
open Erdos972CenteredRowScales

set_option maxHeartbeats 1500000
attribute [local irreducible] root64

def mobiusCutoff (u : ℕ) : ℕ := root64 (root64 u)
def mangoldtCutoff (u : ℕ) : ℕ := mobiusCutoff u ^ 3

lemma mobiusCutoff_tendsto : Tendsto mobiusCutoff atTop atTop := by
  simpa only [mobiusCutoff, Function.comp_def] using root64_tendsto.comp root64_tendsto

lemma asymmetric_cutoffs_bounds {u : ℕ} (hu : 0 < u) :
    0 < mobiusCutoff u ∧ mobiusCutoff u * mangoldtCutoff u ≤ root64 u ∧
      mobiusCutoff u ^ 2 ≤ u := by
  have hv := (root64_bounds hu).1
  obtain ⟨hU, hU64, _⟩ := root64_bounds hv
  change 0 < mobiusCutoff u at hU
  change mobiusCutoff u ^ 64 ≤ root64 u at hU64
  refine ⟨hU, ?_, ?_⟩
  · calc
      _ = mobiusCutoff u ^ 4 := by unfold mangoldtCutoff; ring
      _ ≤ mobiusCutoff u ^ 64 := Nat.pow_le_pow_right hU (by norm_num)
      _ ≤ _ := hU64
  · exact (Nat.pow_le_pow_right hU (by norm_num : 2 ≤ 64)).trans
      (hU64.trans (root64_le u))

lemma cutoff_log_div_tendsto (C : ℝ) (hC : 0 < C) (k : ℕ) :
    Tendsto (fun u : ℕ => C * (1 + Real.log u)^k / (mobiusCutoff u : ℝ))
      atTop (𝓝 0) := by
  have hh := (root64_log_div_tendsto (C * 65^k) (by positivity) k).comp root64_tendsto
  apply squeeze_zero_norm' _ hh
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with u hu
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity [Real.log_natCast_nonneg u])]
  have hlog := root64_log_bound hu
  change _ ≤ C * 65^k * (1 + Real.log (root64 u))^k / (mobiusCutoff u : ℝ)
  have hpow := pow_le_pow_left₀ (by positivity [Real.log_natCast_nonneg u]) hlog k
  calc
    _ ≤ C * (65 * (1 + Real.log (root64 u)))^k / (mobiusCutoff u : ℝ) := by
      gcongr
    _ = _ := by rw [mul_pow]; ring

lemma log_div_self_tendsto (C : ℝ) (hC : 0 < C) (k : ℕ) :
    Tendsto (fun u : ℕ => C * (1 + Real.log u)^k / (u : ℝ)) atTop (𝓝 0) := by
  apply squeeze_zero_norm' _ (root64_log_div_tendsto C hC k)
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with u hu
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity [Real.log_natCast_nonneg u])]
  exact div_le_div_of_nonneg_left (by positivity [Real.log_natCast_nonneg u])
    (Nat.cast_pos.mpr (root64_bounds hu).1) (Nat.cast_le.mpr (root64_le u))

noncomputable def diagonalBudget (α : ℝ) (u : ℕ) : ℝ :=
  1440 * (1 + Real.log u)^2 / (mobiusCutoff u : ℝ) +
    400000 * α * (1 + Real.log u)^3 / (u : ℝ)

lemma diagonalBudget_tendsto {α : ℝ} (hα : 0 < α) :
    Tendsto (diagonalBudget α) atTop (𝓝 0) := by
  have hh := (cutoff_log_div_tendsto 1440 (by norm_num) 2).add
    (log_div_self_tendsto (400000 * α) (by positivity) 3)
  simpa only [diagonalBudget, add_zero] using hh

/-- Numerical budget calculation, separated from the arithmetic row count. -/
lemma normalized_budget_bound {u U N q L A t : ℝ}
    (hu : 1 ≤ u) (hU : 1 ≤ U) (hUu : U^2 ≤ u)
    (hN : 0 < N) (hq : 0 < q) (hL : 1 ≤ L) (hA : 0 < A)
    (hlog : 0 ≤ t) (hlogL : t ≤ 6 * L)
    (hqi : 1 / q ≤ 2 * A / u^4) (hqN : q / N ≤ 64 * A / u^2)
    {s : ℝ} (hs0 : 0 ≤ s) (hsL : s ≤ 7 * L) :
    (U + 1)^2 * t^2 * (10 * N / U^3 + (2 * N / q + 5 * q) * s + 2 * q) / N ≤
      1440 * L^2 / U + 400000 * A * L^3 / u := by
  have hu0 : 0 < u := by linarith
  have hU0 : 0 < U := by linarith
  have hL0 : 0 ≤ L := by linarith
  have hU2 : (U + 1)^2 ≤ 4 * U^2 := by nlinarith only [hU]
  have hlog2 : t^2 ≤ 36 * L^2 := by nlinarith only [hlog, hlogL, hL]
  have hpre : (U + 1)^2 * t^2 ≤ 144 * U^2 * L^2 := by
    have hh := mul_le_mul hU2 hlog2 (sq_nonneg _) (by positivity)
    nlinarith only [hh]
  have hq2 : 2 / q ≤ 4 * A / u^4 := by
    have hh := mul_le_mul_of_nonneg_left hqi (by norm_num : (0 : ℝ) ≤ 2)
    convert hh using 1 <;> ring
  have hq5 : 5 * q / N ≤ 320 * A / u^2 := by
    have hh := mul_le_mul_of_nonneg_left hqN (by norm_num : (0 : ℝ) ≤ 5)
    convert hh using 1 <;> ring
  have hqtail : 2 * q / N ≤ 128 * A / u^2 := by
    have hh := mul_le_mul_of_nonneg_left hqN (by norm_num : (0 : ℝ) ≤ 2)
    convert hh using 1 <;> ring
  have hratio2 : U^2 / u^2 ≤ 1 / u := by
    calc
      _ ≤ u / u^2 := div_le_div_of_nonneg_right hUu (sq_nonneg u)
      _ = _ := by field_simp
  have hratio4 : U^2 / u^4 ≤ 1 / u := by
    apply (div_le_div_iff₀ (pow_pos hu0 4) hu0).mpr
    have hu24 : u^2 ≤ u^4 := pow_le_pow_right₀ hu (by norm_num)
    have hh := mul_le_mul_of_nonneg_right hUu hu0.le
    nlinarith only [hh, hu24]
  have hL23 : L^2 ≤ L^3 := pow_le_pow_right₀ hL (by norm_num)
  calc
    _ = (U + 1)^2 * t^2 * (10 / U^3 + (2 / q + 5 * q / N) * s + 2 * q / N) := by
      field_simp
    _ ≤ 144 * U^2 * L^2 *
        (10 / U^3 + (4 * A / u^4 + 320 * A / u^2) * (7 * L) + 128 * A / u^2) := by
      apply mul_le_mul hpre
      · exact add_le_add (add_le_add le_rfl
          (mul_le_mul (add_le_add hq2 hq5) hsL hs0 (by positivity))) hqtail
      · positivity
      · positivity
    _ = 1440 * L^2 / U +
        4032 * A * L^3 * (U^2 / u^4) +
        322560 * A * L^3 * (U^2 / u^2) +
        18432 * A * L^2 * (U^2 / u^2) := by
      field_simp
      ring
    _ ≤ 1440 * L^2 / U +
        4032 * A * L^3 * (1 / u) +
        322560 * A * L^3 * (1 / u) +
        18432 * A * L^3 * (1 / u) := by
      gcongr
    _ ≤ _ := by
      have hh : 0 ≤ A * L^3 / u := by positivity
      have hc := mul_le_mul_of_nonneg_right (show (345024 : ℝ) ≤ 400000 by norm_num) hh
      convert add_le_add_left hc (1440 * L^2 / U) using 1 <;> ring

lemma log_denominator_bound {u q : ℕ} (hu : 0 < u) (hq : 0 < q)
    (hqu : (q : ℝ) ≤ 32 * (u : ℝ)^4) :
    1 + Real.log (2 * q : ℕ) ≤ 7 * (1 + Real.log u) := by
  have huR : (0 : ℝ) < u := Nat.cast_pos.mpr hu
  have hqR : (0 : ℝ) < q := Nat.cast_pos.mpr hq
  have hlog := Real.log_le_log (show (0 : ℝ) < 2 * q by positivity)
    (mul_le_mul_of_nonneg_left hqu (show (0 : ℝ) ≤ 2 by norm_num))
  have he : (2 : ℝ) * (32 * (u : ℝ)^4) = 64 * (u : ℝ)^4 := by ring
  rw [he, Real.log_mul (x := 64) (y := (u : ℝ)^4) (by norm_num) (by positivity), Real.log_pow] at hlog
  have h64 : Real.log 64 ≤ 6 := by
    have h2 : Real.log 2 ≤ 1 := by
      simpa only [show (2 : ℝ) - 1 = 1 by norm_num] using Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    rw [show (64 : ℝ) = 2^6 by norm_num, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith
  push_cast
  norm_num only [Nat.cast_ofNat] at hlog
  linarith [Real.log_natCast_nonneg u]

/-- Uniform application of the finite arithmetic estimate at the established
main cutoff, for every approximant with the displayed denominator bounds. -/
theorem scale_diagonal_bound {α : ℝ} (hα : 1 ≤ α) {u a q : ℕ}
    (hu : 0 < u) (hαu : α ≤ u) (hq : 0 < q) (haq : a.Coprime q)
    (hqlo : (u : ℝ)^4 ≤ 2 * α * q) (hqhi : (q : ℝ) ≤ 32 * (u : ℝ)^4)
    (happrox : |α - (a : ℝ) / q| * (scaleCutoff α u : ℝ) ≤ 1)
    (hNsq : scaleCutoff α u ≤ q^2) :
    |vaughanDiagonal α (scaleCutoff α u) (mobiusCutoff u) (mangoldtCutoff u)| /
      (scaleCutoff α u : ℝ) ≤ diagonalBudget α u := by
  have hα0 : 0 < α := by linarith
  have huR : (0 : ℝ) < u := Nat.cast_pos.mpr hu
  have hu1 : (1 : ℝ) ≤ u := by exact_mod_cast hu
  have hqR : (0 : ℝ) < q := Nat.cast_pos.mpr hq
  obtain ⟨hU0, hUV, hUu⟩ := asymmetric_cutoffs_bounds hu
  have hUR : (1 : ℝ) ≤ mobiusCutoff u := by exact_mod_cast hU0
  have hUuR : (mobiusCutoff u : ℝ)^2 ≤ u := by exact_mod_cast hUu
  obtain ⟨huN, hNu, hscale⟩ := scaleCutoff_bounds hα hu hαu
  have hN0 : 0 < scaleCutoff α u := hu.trans_le huN
  have hNR : (0 : ℝ) < scaleCutoff α u := Nat.cast_pos.mpr hN0
  have hqi : 1 / (q : ℝ) ≤ 2 * α / (u : ℝ)^4 :=
    (div_le_div_iff₀ hqR (pow_pos huR 4)).mpr (by simpa using hqlo)
  have hqN : (q : ℝ) / (scaleCutoff α u : ℝ) ≤ 64 * α / (u : ℝ)^2 := by
    apply (div_le_div_iff₀ hNR (pow_pos huR 2)).mpr
    have hh := mul_le_mul_of_nonneg_right hqhi (sq_nonneg (u : ℝ))
    have he : (u : ℝ)^4 * (u : ℝ)^2 = (u : ℝ)^6 := by ring
    nlinarith only [hh, hscale, he]
  have hLN : Real.log (scaleCutoff α u) ≤ 6 * (1 + Real.log u) := by
    have hh := Real.log_le_log hNR (Nat.cast_le.mpr hNu)
    rw [Nat.cast_pow, Real.log_pow] at hh
    norm_num only [Nat.cast_ofNat] at hh
    linarith
  have hL : (1 : ℝ) ≤ 1 + Real.log u := by linarith [Real.log_natCast_nonneg u]
  have hlogq := log_denominator_bound hu hq hqhi
  have hnum := normalized_budget_bound hu1 hUR hUuR hNR hqR hL hα0
    (Real.log_natCast_nonneg (scaleCutoff α u)) hLN hqi hqN
    (show 0 ≤ 1 + Real.log (2 * q : ℕ) by linarith [Real.log_natCast_nonneg (2*q)]) hlogq
  have hb := vaughan_diagonal_bound (U := mobiusCutoff u) hα0.le hq haq happrox hNsq
    (show 0 < mangoldtCutoff u by unfold mangoldtCutoff; positivity)
  have hb' := div_le_div_of_nonneg_right hb hNR.le
  simp only [mangoldtCutoff, Nat.cast_pow] at hb'
  exact hb'.trans hnum

/-- The diagonal becomes arbitrarily small uniformly over these admissible
approximants, while the product of the two growing cutoffs remains eligible. -/
theorem eventually_small_diagonal {α : ℝ} (hα : 1 ≤ α) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ u : ℕ in atTop, ∀ a q : ℕ, 0 < q → a.Coprime q →
      (u : ℝ)^4 ≤ 2 * α * q → (q : ℝ) ≤ 32 * (u : ℝ)^4 →
      |α - (a : ℝ) / q| * (scaleCutoff α u : ℝ) ≤ 1 →
      scaleCutoff α u ≤ q^2 →
      |vaughanDiagonal α (scaleCutoff α u) (mobiusCutoff u) (mangoldtCutoff u)| ≤
        ε * (scaleCutoff α u : ℝ) := by
  have hb := (tendsto_order.mp (diagonalBudget_tendsto (show 0 < α by linarith))).2 ε hε
  filter_upwards [hb, eventually_ge_atTop (1 : ℕ), eventually_ge_atTop ⌈α⌉₊]
    with u hu hu1 huα
  intro a q hq haq hqlo hqhi happrox hNsq
  have hαu : α ≤ u := (Nat.le_ceil α).trans (Nat.cast_le.mpr huα)
  have hh := (scale_diagonal_bound hα hu1 hαu hq haq hqlo hqhi happrox hNsq).trans hu.le
  have hN0 : 0 < scaleCutoff α u := hu1.trans (scaleCutoff_bounds hα hu1 hαu).1
  exact (div_le_iff₀ (Nat.cast_pos.mpr hN0)).mp hh

#print axioms asymmetric_cutoffs_bounds
#print axioms diagonalBudget_tendsto
#print axioms normalized_budget_bound
#print axioms scale_diagonal_bound
#print axioms eventually_small_diagonal

end Erdos972AsymmetricDiagonalBudget
