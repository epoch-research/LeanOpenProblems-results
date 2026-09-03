import Submission.FourFactorDiagonalSplit
import Submission.PrimeFactorErrorScales

/-! The prime-restricted common-factor diagonal is o(N), uniformly in the
same rational approximation data as the original diagonal estimate. -/
namespace Erdos972PrimeFactorDiagonalScales
open Filter
open scoped Topology
open Erdos972FourFactorDiagonalSplit Erdos972AsymmetricDiagonalBudget
open Erdos972CenteredRowScales Erdos972GrowingTypeI Erdos972PolynomialRowScales
set_option maxHeartbeats 1500000
attribute [local irreducible] root64

/-- Uniform application of the finite arithmetic estimate at the established
main cutoff, for every approximant with the displayed denominator bounds. -/
theorem scale_prime_diagonal_bound {α : ℝ} (hα : 1 ≤ α) {u a q : ℕ}
    (hu : 0 < u) (hαu : α ≤ u) (hq : 0 < q) (haq : a.Coprime q)
    (hqlo : (u : ℝ)^4 ≤ 2 * α * q) (hqhi : (q : ℝ) ≤ 32 * (u : ℝ)^4)
    (happrox : |α - (a : ℝ) / q| * (scaleCutoff α u : ℝ) ≤ 1)
    (hNsq : scaleCutoff α u ≤ q^2) :
    |primeVaughanDiagonal α (scaleCutoff α u) (mobiusCutoff u) (mangoldtCutoff u)| /
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
  have hb := prime_vaughan_diagonal_bound (U := mobiusCutoff u) hα0.le hq haq happrox hNsq
    (show 0 < mangoldtCutoff u by unfold mangoldtCutoff; positivity)
  have hb' := div_le_div_of_nonneg_right hb hNR.le
  simp only [mangoldtCutoff, Nat.cast_pow] at hb'
  exact hb'.trans hnum

/-- The diagonal becomes arbitrarily small uniformly over these admissible
approximants, while the product of the two growing cutoffs remains eligible. -/
theorem eventually_small_prime_diagonal {α : ℝ} (hα : 1 ≤ α) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ u : ℕ in atTop, ∀ a q : ℕ, 0 < q → a.Coprime q →
      (u : ℝ)^4 ≤ 2 * α * q → (q : ℝ) ≤ 32 * (u : ℝ)^4 →
      |α - (a : ℝ) / q| * (scaleCutoff α u : ℝ) ≤ 1 →
      scaleCutoff α u ≤ q^2 →
      |primeVaughanDiagonal α (scaleCutoff α u) (mobiusCutoff u) (mangoldtCutoff u)| ≤
        ε * (scaleCutoff α u : ℝ) := by
  have hb := (tendsto_order.mp (diagonalBudget_tendsto (show 0 < α by linarith))).2 ε hε
  filter_upwards [hb, eventually_ge_atTop (1 : ℕ), eventually_ge_atTop ⌈α⌉₊]
    with u hu hu1 huα
  intro a q hq haq hqlo hqhi happrox hNsq
  have hαu : α ≤ u := (Nat.le_ceil α).trans (Nat.cast_le.mpr huα)
  have hh := (scale_prime_diagonal_bound hα hu1 hαu hq haq hqlo hqhi happrox hNsq).trans hu.le
  have hN0 : 0 < scaleCutoff α u := hu1.trans (scaleCutoff_bounds hα hu1 hαu).1
  exact (div_le_iff₀ (Nat.cast_pos.mpr hN0)).mp hh

#print axioms scale_prime_diagonal_bound
#print axioms eventually_small_prime_diagonal
end Erdos972PrimeFactorDiagonalScales
