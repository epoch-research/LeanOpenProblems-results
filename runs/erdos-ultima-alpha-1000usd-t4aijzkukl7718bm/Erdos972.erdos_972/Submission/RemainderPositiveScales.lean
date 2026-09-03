import Submission.RemainderPositiveBudget
import Submission.RemainderVarianceScales

/-! The positive part of the actual Vaughan remainder has linear mass at
the same power-growing cutoffs used in the main four-factor reduction. -/
namespace Erdos972RemainderPositiveScales

open Finset Filter ArithmeticFunction
open scoped Topology
open Erdos972DoubleVaughan Erdos972RemainderPositiveBudget
open Erdos972PrimeIntervalCounts Erdos972PrimeReciprocalBands
open Erdos972ChebyshevPNT Erdos972GrowingTypeIIReduction
open Erdos972CenteredRowScales Erdos972RemainderVarianceScales
open Erdos972CovarianceScaleBudgets

set_option maxHeartbeats 1000000
set_option exponentiation.threshold 1024

lemma positiveMass_power_bands {k W B N : ℕ} (hk : 3 ≤ k)
    (hWlo : 2^(8*k) ≤ W) (hWhi : W < 2^(8*(k+1)))
    (hA : (1/24 : ℝ) ≤ reciprocalPrimeMass (2^(5*k)) (2^(6*k)))
    (hC : (1/28 : ℝ) ≤ reciprocalPrimeMass (2^(6*k)) (2^(7*k)))
    (hN : 4*W^2*max W B ≤ N)
    (hθ : ∀ Q : ℕ, B ≤ Q → (Q : ℝ)/2 ≤ Chebyshev.theta (2*Q : ℕ)-Chebyshev.theta Q) :
    (N : ℝ)/5376 ≤ positiveMass W N := by
  let A := primesBetween (2^(5*k)) (2^(6*k))
  let C := primesBetween (2^(6*k)) (2^(7*k))
  have hA' : ∀ r ∈ A, r.Prime ∧ r ≤ W := by
    intro r hr
    obtain ⟨_, hrmax, hp⟩ := mem_primesBetween.mp hr
    exact ⟨hp, hrmax.trans ((Nat.pow_le_pow_right (by norm_num) (by omega : 6*k ≤ 8*k)).trans hWlo)⟩
  have hC' : ∀ s ∈ C, s.Prime ∧ s ≤ W := by
    intro s hs
    obtain ⟨_, hsmax, hp⟩ := mem_primesBetween.mp hs
    exact ⟨hp, hsmax.trans ((Nat.pow_le_pow_right (by norm_num) (by omega : 7*k ≤ 8*k)).trans hWlo)⟩
  have hsep : ∀ r ∈ A, ∀ s ∈ C, r < s := by
    intro r hr s hs
    exact (mem_primesBetween.mp hr).2.1.trans_lt (mem_primesBetween.mp hs).1
  have hprod : ∀ r ∈ A, ∀ s ∈ C, W < r*s := by
    intro r hr s hs
    have hmul := Nat.mul_le_mul (mem_primesBetween.mp hr).1.le (mem_primesBetween.mp hs).1.le
    rw [← pow_add] at hmul
    exact hWhi.trans_le ((Nat.pow_le_pow_right (by norm_num) (by omega : 8*(k+1) ≤ 5*k+6*k)).trans hmul)
  have hh := positiveMass_lower hA' hC' hsep hprod hN hθ
  have hprodR : (1/24 : ℝ)*(1/28 : ℝ) ≤ reciprocalPrimeMass (2^(5*k)) (2^(6*k))*
      reciprocalPrimeMass (2^(6*k)) (2^(7*k)) :=
    mul_le_mul hA hC (by norm_num) (reciprocalPrimeMass_nonneg _ _)
  calc
    _ = ((N : ℝ)/8)*((1/24 : ℝ)*(1/28 : ℝ)) := by ring
    _ ≤ ((N : ℝ)/8)*(reciprocalPrimeMass (2^(5*k)) (2^(6*k))*
      reciprocalPrimeMass (2^(6*k)) (2^(7*k))) :=
      mul_le_mul_of_nonneg_left hprodR (by positivity)
    _ ≤ _ := by simpa only [mul_assoc, reciprocalPrimeMass] using hh

/-- Choosing bands logarithmically allows the preceding estimate to apply
at every sufficiently large cutoff, not just powers of two. -/
def bandIndex (W : ℕ) : ℕ := Nat.log 2 W/8

lemma bandIndex_bounds {W : ℕ} (hW : 0 < W) :
    2^(8*bandIndex W) ≤ W ∧ W < 2^(8*(bandIndex W+1)) := by
  constructor
  · exact (Nat.pow_le_pow_right (by norm_num) (Nat.mul_div_le (Nat.log 2 W) 8)).trans
      (Nat.pow_log_le_self 2 hW.ne')
  · have hh := Nat.lt_pow_succ_log_self (by norm_num : 1 < (2:ℕ)) W
    apply hh.trans_le
    apply Nat.pow_le_pow_right (by norm_num)
    dsimp only [bandIndex]
    have hdiv := Nat.lt_mul_div_succ (Nat.log 2 W) (by norm_num : 0 < (8:ℕ))
    omega

lemma bandIndex_tendsto : Tendsto bandIndex atTop atTop := by
  apply tendsto_atTop.2
  intro B
  filter_upwards [eventually_ge_atTop ((2 : ℕ)^(8*B))] with W hW
  have hh := Nat.le_log_of_pow_le (by norm_num : 1 < (2:ℕ)) hW
  exact (Nat.le_div_iff_mul_le (by norm_num : 0 < (8:ℕ))).mpr (by omega)

lemma eventually_dyadic_prime_log_mass :
    ∀ᶠ Q : ℕ in atTop, (Q : ℝ)/2 ≤ Chebyshev.theta (2*Q : ℕ)-Chebyshev.theta Q := by
  have hh := tendsto_natCast_atTop_atTop.eventually
    (eventually_theta_interval_lower (a := 1) (b := 2) (by norm_num) (by norm_num))
  filter_upwards [hh] with Q hQ
  norm_num only [sub_self, sub_zero, one_mul, Nat.cast_ofNat] at hQ
  convert hQ using 1 <;> push_cast <;> ring

/-- A quantitative obstruction to discarding all positive values of the
remainder as an o(N) error. This does not bound its signed Beatty covariance. -/
theorem eventually_positiveMass_lower {α : ℝ} (hα : 1 ≤ α) :
    ∀ᶠ u : ℕ in atTop, (scaleCutoff α u : ℝ)/5376 ≤
      positiveMass (growingCutoff u) (scaleCutoff α u) := by
  obtain ⟨B, hB⟩ := eventually_atTop.mp eventually_dyadic_prime_log_mass
  have hk := bandIndex_tendsto.comp growingCutoff_tendsto
  filter_upwards [hk.eventually_ge_atTop 3, hk.eventually eventually_two_reciprocal_bands,
    growingCutoff_tendsto.eventually_ge_atTop (max B 4),
    eventually_ge_atTop (1 : ℕ), eventually_ge_atTop ⌈2*α⌉₊] with u hu hbands hW hu0 huα
  have hW4 : 4 ≤ growingCutoff u := (le_max_right B 4).trans hW
  have hWB : B ≤ growingCutoff u := (le_max_left B 4).trans hW
  have hW0 : 0 < growingCutoff u := by omega
  have hpow := growingCutoff_main_power hα hu0 ((Nat.le_ceil _).trans (Nat.cast_le.mpr huα))
  obtain ⟨hlo, hhi⟩ := bandIndex_bounds hW0
  apply positiveMass_power_bands hu hlo hhi hbands.1 hbands.2 _ hB
  rw [max_eq_left hWB]
  apply le_trans _ hpow
  calc
    _ ≤ (growingCutoff u)^4 := by nlinarith only [hW4, sq_nonneg ((growingCutoff u : ℤ)-4)]
    _ ≤ _ := Nat.pow_le_pow_right hW0 (by decide : 4 ≤ 640)

theorem not_tendsto_positiveMass_zero {α : ℝ} (hα : 1 ≤ α) :
    ¬ Tendsto (fun u : ℕ => positiveMass (growingCutoff u) (scaleCutoff α u)/scaleCutoff α u)
      atTop (𝓝 0) := by
  intro hlim
  obtain ⟨u, hu, hlower, hN⟩ := (((tendsto_order.mp hlim).2 (1/10752) (by norm_num)).and
    ((eventually_positiveMass_lower hα).and ((scaleCutoff_tendsto hα).eventually_ge_atTop 1))).exists
  have hNR : (0 : ℝ) < scaleCutoff α u := Nat.cast_pos.mpr hN
  have hh : (1/5376 : ℝ) ≤ positiveMass (growingCutoff u) (scaleCutoff α u)/scaleCutoff α u := by
    apply (le_div_iff₀ hNR).mpr
    simpa only [div_eq_mul_inv, one_mul, mul_comm] using hlower
  nlinarith only [hu, hh]

#print axioms eventually_positiveMass_lower
#print axioms not_tendsto_positiveMass_zero

end Erdos972RemainderPositiveScales
