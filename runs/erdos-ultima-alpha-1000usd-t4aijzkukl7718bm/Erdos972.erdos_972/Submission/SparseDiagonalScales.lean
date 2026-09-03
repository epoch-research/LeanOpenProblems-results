import Submission.SparseVaughanDiagonal
import Submission.AsymmetricDiagonalBudget

/-! Vanishing sparse-diagonal budget, uniform in the Mobius cutoff. -/
namespace Erdos972SparseDiagonalScales
open Filter ArithmeticFunction
open scoped Topology ArithmeticFunction.Moebius ArithmeticFunction.zeta
open Erdos972SparseVaughanDiagonal Erdos972SparseCommonDivisorSupport
open Erdos972AsymmetricDiagonalBudget Erdos972CenteredRowScales
open Erdos972CovarianceScaleBudgets Erdos972PolynomialRowScales
open Erdos972PrimePowerError Erdos972GrowingTypeIIReduction Erdos972Vaughan
set_option maxHeartbeats 1500000
attribute [local irreducible] root64

lemma common_divisor_scale_density {α : ℝ} (hα : 1 ≤ α) {u a q V : ℕ}
    (hu : 0 < u) (hαu : α ≤ u) (hV : mobiusCutoff u ≤ V)
    (hq : 0 < q) (haq : a.Coprime q)
    (hqlo : (u : ℝ)^4 ≤ 2*α*q) (hqhi : (q : ℝ) ≤ 32*(u : ℝ)^4)
    (happrox : |α-(a : ℝ)/q| * (scaleCutoff α u : ℝ) ≤ 1) (hNsq : scaleCutoff α u ≤ q^2) :
    ((commonDivisorSet α (scaleCutoff α u) V).card : ℝ)/(scaleCutoff α u : ℝ) ≤
      10/(mobiusCutoff u : ℝ)+2400*α*(1+Real.log u)/(u : ℝ) := by
  have hα0 : 0 < α := by linarith
  have huR : (0 : ℝ) < u := Nat.cast_pos.mpr hu
  have hu1 : (1 : ℝ) ≤ u := by exact_mod_cast hu
  have hqR : (0 : ℝ) < q := Nat.cast_pos.mpr hq
  have hZ : 0 < mobiusCutoff u := (asymmetric_cutoffs_bounds hu).1
  have hVR : (0 : ℝ) < V := Nat.cast_pos.mpr (hZ.trans_le hV)
  obtain ⟨huN, hNu, hscale⟩ := scaleCutoff_bounds hα hu hαu
  have hNR : (0 : ℝ) < scaleCutoff α u := Nat.cast_pos.mpr (hu.trans_le huN)
  have hqi : 1/(q : ℝ) ≤ 2*α/(u : ℝ)^4 :=
    (div_le_div_iff₀ hqR (pow_pos huR 4)).mpr (by simpa using hqlo)
  have hqN : (q : ℝ)/(scaleCutoff α u : ℝ) ≤ 64*α/(u : ℝ)^2 := by
    apply (div_le_div_iff₀ hNR (pow_pos huR 2)).mpr
    have hh := mul_le_mul_of_nonneg_right hqhi (sq_nonneg (u : ℝ))
    have he : (u : ℝ)^4*(u : ℝ)^2 = (u : ℝ)^6 := by ring
    nlinarith only [hh, hscale, he]
  have hu4 : (u : ℝ) ≤ (u : ℝ)^4 := by simpa using pow_le_pow_right₀ hu1 (by norm_num : 1 ≤ 4)
  have hu2 : (u : ℝ) ≤ (u : ℝ)^2 := by simpa using pow_le_pow_right₀ hu1 (by norm_num : 1 ≤ 2)
  have hqi' : 1/(q : ℝ) ≤ 2*α/(u : ℝ) := hqi.trans
    (div_le_div_of_nonneg_left (by positivity) huR hu4)
  have hqN' : (q : ℝ)/(scaleCutoff α u : ℝ) ≤ 64*α/(u : ℝ) := hqN.trans
    (div_le_div_of_nonneg_left (by positivity) huR hu2)
  have hL : 1 ≤ 1+Real.log u := by linarith [Real.log_natCast_nonneg u]
  have hs := log_denominator_bound hu hq hqhi
  have hb := div_le_div_of_nonneg_right
    (commonDivisorSet_card_bound hα0.le hq haq happrox hNsq (hZ.trans_le hV)) hNR.le
  apply hb.trans
  calc
    _ = 10/(V : ℝ)+(2/(q : ℝ)+5*((q : ℝ)/(scaleCutoff α u : ℝ)))*
        (1+Real.log (2*q : ℕ))+2*((q : ℝ)/(scaleCutoff α u : ℝ)) := by field_simp
    _ ≤ 10/(mobiusCutoff u : ℝ)+(2*(2*α/(u : ℝ))+5*(64*α/(u : ℝ)))*
        (7*(1+Real.log u))+2*(64*α/(u : ℝ)) := by
      have hqi2 : 2/(q : ℝ) ≤ 2*(2*α/(u : ℝ)) := by
        convert mul_le_mul_of_nonneg_left hqi' (by norm_num : (0 : ℝ) ≤ 2) using 1 <;> ring
      gcongr
    _ = 10/(mobiusCutoff u : ℝ)+2268*(α*(1+Real.log u)/(u : ℝ))+128*(α/(u : ℝ)) := by ring
    _ ≤ 10/(mobiusCutoff u : ℝ)+2396*(α*(1+Real.log u)/(u : ℝ)) := by
      have hl : α/(u : ℝ) ≤ α*(1+Real.log u)/(u : ℝ) :=
        div_le_div_of_nonneg_right (le_mul_of_one_le_right hα0.le hL) huR.le
      nlinarith only [hl]
    _ ≤ 10/(mobiusCutoff u : ℝ)+2400*(α*(1+Real.log u)/(u : ℝ)) := by
      gcongr <;> norm_num
    _ = _ := by ring

noncomputable def sparseDiagonalBudget (α : ℝ) (u : ℕ) : ℝ :=
  α*(6^19*(10*(1+Real.log u)^19/(mobiusCutoff u : ℝ)+
    2400*α*(1+Real.log u)^20/(u : ℝ)))^2

lemma sparseDiagonalBudget_tendsto {α : ℝ} (hα : 0 < α) :
    Tendsto (sparseDiagonalBudget α) atTop (𝓝 0) := by
  have hh := ((((cutoff_log_div_tendsto 10 (by norm_num) 19).add
    (log_div_self_tendsto (2400*α) (by positivity) 20)).const_mul (6^19)).pow 2).const_mul α
  simpa only [sparseDiagonalBudget, add_zero, mul_zero, zero_pow (by norm_num : 2 ≠ 0)] using hh

theorem sparse_diagonal_scale_fourth {α : ℝ} (hα : 1 ≤ α) {u a q U V : ℕ}
    (hu : 0 < u) (hαu : α ≤ u) (hV : mobiusCutoff u ≤ V)
    (hq : 0 < q) (haq : a.Coprime q)
    (hqlo : (u : ℝ)^4 ≤ 2*α*q) (hqhi : (q : ℝ) ≤ 32*(u : ℝ)^4)
    (happrox : |α-(a : ℝ)/q| * (scaleCutoff α u : ℝ) ≤ 1) (hNsq : scaleCutoff α u ≤ q^2)
    (g : ArithmeticFunction ℝ) (hg : ∀ p, 0 ≤ g p) (hgΛ : ∀ p, g p ≤ Λ p) :
    |Erdos972FourFactorDiagonalSplit.factorDiagonal α (scaleCutoff α u)
      (tail (μ : ArithmeticFunction ℝ) U*ζ) (tail g V)/(scaleCutoff α u : ℝ)|^4 ≤ sparseDiagonalBudget α u := by
  let N := scaleCutoff α u
  have hN : 0 < N := hu.trans_le (scaleCutoff_bounds hα hu hαu).1
  have hN0 : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hL : 0 ≤ 1+Real.log u := by linarith [Real.log_natCast_nonneg u]
  have hs := (scale_log_bound hα hu hαu).2
  have hiL : 1+Real.log N ≤ 6*(1+Real.log u) :=
    (add_le_add le_rfl (Real.log_le_log hN0 (le_mul_of_one_le_left hN0.le hα))).trans hs
  have hoL : 1+Real.log (floorMul α N) ≤ 6*(1+Real.log u) :=
    (add_le_add le_rfl (Real.log_le_log (Nat.cast_pos.mpr (floorMul_pos hα hN))
      (floorMul_le_real hα (le_refl N)))).trans hs
  have hd := common_divisor_scale_density hα hu hαu hV hq haq hqlo hqhi happrox hNsq
  have hh := sparse_diagonal_normalized_fourth (U := U) (V := V) hα hN hiL hoL g hg hgΛ
  apply hh.trans
  calc
    _ ≤ α*(10/(mobiusCutoff u : ℝ)+2400*α*(1+Real.log u)/(u : ℝ))^2*
        (6*(1+Real.log u))^38 := by gcongr
    _ = _ := by unfold sparseDiagonalBudget; ring

theorem eventually_small_sparse_diagonal {α : ℝ} (hα : 1 ≤ α) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ u : ℕ in atTop, ∀ a q U V : ℕ, mobiusCutoff u ≤ V → 0 < q → a.Coprime q →
      (u : ℝ)^4 ≤ 2*α*q → (q : ℝ) ≤ 32*(u : ℝ)^4 →
      |α-(a : ℝ)/q| * (scaleCutoff α u : ℝ) ≤ 1 → scaleCutoff α u ≤ q^2 →
      ∀ g : ArithmeticFunction ℝ, (∀ p, 0 ≤ g p) → (∀ p, g p ≤ Λ p) →
      |Erdos972FourFactorDiagonalSplit.factorDiagonal α (scaleCutoff α u)
        (tail (μ : ArithmeticFunction ℝ) U*ζ) (tail g V)| ≤ ε*(scaleCutoff α u : ℝ) := by
  filter_upwards [eventually_ge_atTop (1 : ℕ), eventually_ge_atTop ⌈α⌉₊,
    (tendsto_order.mp (sparseDiagonalBudget_tendsto (show 0 < α by linarith))).2 (ε^4) (pow_pos hε 4)]
    with u hu huα hbudget
  intro a q U V hV hq haq hqlo hqhi happrox hNsq g hg hgΛ
  have hαu : α ≤ u := (Nat.le_ceil α).trans (Nat.cast_le.mpr huα)
  have hN0 : (0 : ℝ) < scaleCutoff α u := Nat.cast_pos.mpr (hu.trans (scaleCutoff_bounds hα hu hαu).1)
  have hh := (sparse_diagonal_scale_fourth (U := U) hα hu hαu hV hq haq hqlo hqhi happrox hNsq g hg hgΛ).trans hbudget.le
  have hs := (pow_le_pow_iff_left₀ (abs_nonneg _) hε.le (by norm_num : 4 ≠ 0)).mp hh
  rw [abs_div, abs_of_pos hN0] at hs
  exact (div_le_iff₀ hN0).mp hs

#print axioms common_divisor_scale_density
#print axioms sparseDiagonalBudget_tendsto
#print axioms eventually_small_sparse_diagonal
end Erdos972SparseDiagonalScales
