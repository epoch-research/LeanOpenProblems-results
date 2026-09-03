import Submission.TwoLeastFactorMoment
import Submission.PrimeLeastFactorScales

/-! The two-least-distinct-factor moment on actual prime inputs at arbitrary
large irrational scales, and a one-sided smoothed comparison. -/
namespace Erdos972PrimeTwoLeastFactorScales

open Finset Filter ArithmeticFunction
open Erdos972TwoLeastPrimeFactors Erdos972TwoLeastFactorMoment
open Erdos972LeastFactorSieve Erdos972LeastFactorCutoff Erdos972PrimeLeastFactorScales
open Erdos972PrimeRoughOutputs Erdos972PrimePowerError Erdos972ChebyshevRowMean
open Erdos972SelbergLowerTest Erdos972PolynomialRowScales Erdos972PrimeRotation
open Erdos972DualPrimeRows Erdos972ScaledPrimeRows
open Erdos972SmoothMangoldt
set_option maxHeartbeats 5000000
set_option exponentiation.threshold 8192
set_option autoImplicit false
attribute [local irreducible] root64

noncomputable def primeTwoLeastFactorMoment (α : ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Ioc 0 N, primeWeight n*twoLeastCost (floorMul α n)

/-- A finite estimate with all the required row and cutoff conditions exposed. -/
theorem prime_twoLeast_factor_bound {α : ℝ} (hα : 1 ≤ α) {u : ℕ} (hu : 0 < u)
    (hW : 2 ≤ Nat.sqrt (Nat.sqrt (root64 u)))
    (hαZ : α ≤ layerCutoff u)
    (hbudget : primeRowError u ≤ (u^6 : ℕ)/(16*(root64 u:ℝ)))
    (hrows : ∀ d : ℕ, 0 < d → d ≤ root64 u →
      |row (Ioc 0 (u^6)) primeWeight (floorMul α) d-Chebyshev.psi (u^6 : ℕ)/d| ≤
        primeRowError u) :
    primeTwoLeastFactorMoment α (u^6) ≤ 1000000000*(u:ℝ)^6*Real.log (layerCutoff u) := by
  let Z := layerCutoff u
  let N := u^6
  let X := Chebyshev.psi (N : ℕ)
  let E := primeRowError u
  let L := Real.log (floorMul α N)
  have hZ2 : 2 ≤ Z := logLevel_two_le _
  have hZ1 : 1 ≤ Z := by omega
  have hZpow : Z^4 ≤ root64 u := (layerCutoff_bounds hu hW).1
  have hZmod : Z^3 ≤ root64 u :=
    (Nat.pow_le_pow_right hZ1 (by decide : 3 ≤ 4)).trans hZpow
  have hN0 : 0 < N := Nat.pow_pos hu
  have hN : 0 ≤ (N:ℝ) := Nat.cast_nonneg N
  have hX : 0 ≤ X := Chebyshev.psi_nonneg _
  have hE : 0 ≤ E := primeRowError_nonneg u
  have hL : 0 ≤ L := Real.log_natCast_nonneg _
  have hXup : X ≤ 7*(N:ℝ) := psi_le_seven_mul hN
  have hEup : E*(logLevel (layerCount u):ℝ)^4 ≤ (N:ℝ) := by
    have hv0 : (0:ℝ) < root64 u := Nat.cast_pos.mpr (root64_bounds hu).1
    have hb := (le_div_iff₀ (show 0 < 16*(root64 u:ℝ) by positivity)).mp hbudget
    have hz : (Z:ℝ)^4 ≤ root64 u := by
      simpa only [Nat.cast_pow] using (Nat.cast_le.mpr hZpow : ((Z^4:ℕ):ℝ) ≤ root64 u)
    have hh := mul_le_mul_of_nonneg_left hz hE
    have hn : 0 ≤ E*(root64 u:ℝ) := mul_nonneg hE (Nat.cast_nonneg _)
    change E*(Z:ℝ)^4 ≤ (N:ℝ)
    change E*(16*(root64 u:ℝ)) ≤ (N:ℝ) at hb
    nlinarith only [hb, hh, hn]
  have hLup : L ≤ 5000*Real.log (logLevel (layerCount u)) := by
    have hMpos : 0 < floorMul α N := floorMul_pos hα hN0
    have hb := floor_output_layer_bound hu hW hαZ (le_refl (u^6))
    have hh := Real.log_le_log (Nat.cast_pos.mpr hMpos) (Nat.cast_le.mpr hb)
    rw [Nat.cast_pow, Real.log_pow] at hh
    have hlog : 0 ≤ Real.log Z := Real.log_natCast_nonneg _
    change L ≤ 5000*Real.log Z
    norm_num only [Nat.cast_ofNat] at hh
    change L ≤ 4993*Real.log Z at hh
    linarith only [hh, hlog]
  have hy (n : ℕ) (hn : n ∈ Ioc 0 N) :
      Real.log (secondFac (floorMul α n)) ≤ 5000*Real.log (logLevel (layerCount u)) := by
    have hnpos := floorMul_pos hα (mem_Ioc.mp hn).1
    have hle : secondFac (floorMul α n) ≤ floorMul α N :=
      (secondFac_le_self hnpos).trans ((floorMul_strictMono hα).monotone (mem_Ioc.mp hn).2)
    exact (Erdos972ExponentialSum.monotone_log_natCast hle).trans hLup
  have hh := weighted_twoLeastFactor_linear (Ioc 0 N) primeWeight (floorMul α)
    (fun n _ => primeWeight_nonneg n) (layerCount u) hN hX hE hXup hEup hy
    (fun d hd hdZ => hrows d hd (hdZ.trans hZmod))
  simpa only [primeTwoLeastFactorMoment, N, Nat.cast_pow, layerCutoff] using hh

/-- The actual one-prime rows supply the preceding estimate at arbitrarily
large scales for every prescribed irrational slope. -/
theorem exists_prime_twoLeast_factor_scale {α : ℝ} (hα : 1 < α) (hI : Irrational α) (B : ℕ) :
    ∃ u : ℕ, B < u ∧ B < layerCount u ∧
      primeTwoLeastFactorMoment α (u^6) ≤ 1000000000*(u:ℝ)^6*Real.log (layerCutoff u) := by
  obtain ⟨T, hT⟩ := eventually_atTop.mp
    (eventually_rough_prime_budget.and
      ((root64_tendsto.eventually_ge_atTop 2048).and
        (((nat_fourth_root_tendsto.comp root64_tendsto).eventually_ge_atTop 2).and
          ((layerCutoff_tendsto.eventually_ge_atTop ⌈α⌉₊).and
            (layerCount_tendsto.eventually_gt_atTop B)))))
  let A := max T (B+1)
  obtain ⟨r, hr, hden⟩ := Erdos972RationalRoute.exists_good_approximant_large_den hα hI (A^4)
  let u := Nat.sqrt (Nat.sqrt r.den)
  have hAu : A ≤ u := (le_fourth_root_iff A r.den).mpr hden.le
  have hTu : T ≤ u := (le_max_left T (B+1)).trans hAu
  have hBu : B < u := by have := (le_max_right T (B+1)).trans hAu; omega
  obtain ⟨hu, hlo, hhi⟩ := fourth_root_bounds r.pos
  change 0 < u at hu
  change u^4 ≤ r.den at hlo
  change r.den ≤ 16*u^4 at hhi
  clear_value u
  obtain ⟨⟨_, hbudget⟩, hv, hW, hαZ, hBJ⟩ := hT u hTu
  have hαcut : α ≤ layerCutoff u := (Nat.le_ceil α).trans (Nat.cast_le.mpr hαZ)
  refine ⟨u, hBu, hBJ, prime_twoLeast_factor_bound hα.le hu hW hαcut hbudget ?_⟩
  intro d hd hdv
  exact prime_row_discrepancy α d (u^6) (input_divisor_row_discrepancy
    (show 0 ≤ α by linarith) r hr.le (K := 1) (by norm_num) (by simpa using hv)
    (root64_bounds hu).2.1 (by simpa using hlo) (by simpa using hhi) hd hdv le_rfl)

/-- This one-sided comparison is the direction useful for a lower bound.
It does not pay a deficit on prime or prime-power outputs. -/
theorem mixed_smooth_upper_twoLeast {t : ℝ} (ht : 0 < t) (α : ℝ) (N : ℕ) :
    mixedPrimeSmooth t α N ≤ mixedPrimeMangoldt α N+t*primeTwoLeastFactorMoment α N := by
  have hh := sum_le_sum (fun n (_ : n ∈ Ioc 0 N) => mul_le_mul_of_nonneg_left
    (smooth_le_mangoldt_add_twoLeast ht (floorMul α n)) (primeWeight_nonneg n))
  simp only [mul_add, sum_add_distrib] at hh
  unfold mixedPrimeSmooth mixedPrimeMangoldt primeTwoLeastFactorMoment
  convert hh using 1
  rw [mul_sum]
  congr 1
  apply sum_congr rfl
  intro n hn
  ring

/-- The composite-output error has no log-log factor. The smoothed lower
bound needed to exploit this comparison is still not established. -/
theorem exists_twoLeast_comparison_scale {α : ℝ} (hα : 1 < α) (hI : Irrational α) (B : ℕ) :
    ∃ u : ℕ, B < u ∧ B < layerCount u ∧ ∀ t : ℝ, 0 < t →
      mixedPrimeSmooth t α (u^6)-1000000000*t*(u:ℝ)^6*Real.log (layerCutoff u) ≤
        mixedPrimeMangoldt α (u^6) := by
  obtain ⟨u, hu, hJ, hb⟩ := exists_prime_twoLeast_factor_scale hα hI B
  refine ⟨u, hu, hJ, ?_⟩
  intro t ht
  have hh := mixed_smooth_upper_twoLeast ht α (u^6)
  have hm := mul_le_mul_of_nonneg_left hb ht.le
  nlinarith only [hh, hm]

#print axioms prime_twoLeast_factor_bound
#print axioms exists_prime_twoLeast_factor_scale
#print axioms mixed_smooth_upper_twoLeast
#print axioms exists_twoLeast_comparison_scale
end Erdos972PrimeTwoLeastFactorScales
