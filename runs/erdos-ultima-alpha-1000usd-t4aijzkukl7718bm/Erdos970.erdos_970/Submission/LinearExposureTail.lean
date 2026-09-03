import Submission.GeneralExposureTail
import Submission.ThreeEighthTail
import Submission.HardCubicPowerBound
import Submission.SoftQuadraticLowTail

/-! An unconditional stretched-exponential void bound already at length k,
using sharper factorial exposure and a three-eighths small-prime core.
This does not by itself exclude an exceptional phase. -/
namespace Erdos970.GapAverages
open Finset Real Filter
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

lemma linear_exposure_budget (k t : ℕ) (ht : 0 < t)
    (hroot : t^80 ≤ 2^80*k) (hlarge : fiveHalvesConstant*2^160 ≤ t) :
    IsJacobsthalBound (t^31-1) k := by
  have hj := jacobsthalFunction_sq_le_fifth (t^31) (by positivity)
  have hc : fiveHalvesConstant*2^160 ≤ t^5 :=
    hlarge.trans (Nat.le_self_pow (by omega) t)
  have hp := Nat.pow_le_pow_left hroot 2
  have hh : 2^160 * jacobsthalFunction (t^31)^2 ≤ 2^160*k^2 := by
    calc
      _ ≤ 2^160*(fiveHalvesConstant*(t^31)^5) := Nat.mul_le_mul_left _ hj
      _ = (fiveHalvesConstant*2^160)*t^155 := by ring
      _ ≤ t^5*t^155 := Nat.mul_le_mul_right _ hc
      _ = (t^80)^2 := by ring
      _ ≤ (2^80*k)^2 := hp
      _ = _ := by ring
  have hjk : jacobsthalFunction (t^31) ≤ k := by
    have hh' : jacobsthalFunction (t^31)^2 ≤ k^2 :=
      (mul_le_mul_iff_right₀ (by positivity : 0 < (2 : ℕ)^160)).mp hh
    exact (Nat.pow_le_pow_iff_left (by omega : 2 ≠ 0)).mp hh'
  have hb := (jacobsthalFunction_le_iff (t^31) k).mp hjk
  intro n hn hnk a
  exact hb n hn (hnk.trans (Nat.sub_le _ _)) a

lemma eventually_linear_core_overhead (D : ℕ) :
    ∀ᶠ t : ℕ in atTop, ((D : ℝ)+2)*(3+31*log t) ≤ (t : ℝ)/400 := by
  have hD : (0 : ℝ) < (D : ℝ)+2 := by positivity
  have hs := tendsto_natCast_atTop_atTop.eventually
    (isLittleO_log_id_atTop.def (show (0 : ℝ) < 1/(24800*((D : ℝ)+2)) by positivity))
  have ht := tendsto_natCast_atTop_atTop.eventually
    (eventually_ge_atTop (2400*((D : ℝ)+2)))
  filter_upwards [hs, ht, eventually_ge_atTop 1] with t hs ht ht1
  have ht0 : (0 : ℝ) ≤ t := Nat.cast_nonneg _
  have hl : 0 ≤ log (t : ℝ) := log_nonneg (by exact_mod_cast ht1)
  have hs' : log (t : ℝ) ≤ (t : ℝ)/(24800*((D : ℝ)+2)) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg ht0, abs_of_nonneg hl,
      id_eq, one_div, inv_mul_eq_div] using hs
  have hmul := (le_div_iff₀ (show (0 : ℝ) < 24800*((D : ℝ)+2) by positivity)).mp hs'
  nlinarith

lemma linear_core_envelope (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (k t D : ℕ) (ht : 0 < t) (hcard : P.card ≤ t^80)
    (hD : 1024 ≤ D) (hlogD : 2048*(WeightedMertens.boundConstant+1) ≤ log (D : ℝ))
    (hcost : ((D : ℝ)+2)*(3+31*log t) ≤ (t : ℝ)/400)
    (hb : IsJacobsthalBound (t^31-1) k) :
    coveredFraction P k ≤ exp (-(t : ℝ)^31/400) := by
  let S := P.filter (fun p => p ≤ D*t^30)
  have hSP : S ⊆ P := filter_subset _ _
  have hScard : S.card ≤ D*t^30+1 := by
    have hs : S ⊆ range (D*t^30+1) := by
      intro p hp
      exact mem_range.mpr (by have := (mem_filter.mp hp).2; omega)
    simpa only [card_range] using card_le_card hs
  have htail : (∑ p ∈ P \ S, (p : ℝ)⁻¹) ≤ 199/200 := by
    have he : P \ S = P.filter (fun p => D*t^30 < p) := by
      ext p
      simp only [S, mem_filter]
      by_cases hp : p ∈ P <;> simp [hp]
    rw [he]
    simpa only [one_div] using WeightedMertens.tail_three_eighths P hP t D ht hD hlogD hcard
  have hh := coveredFraction_le_general_core P S hP hSP k (t^31) (by positivity)
    hb (199/200) (by norm_num) htail
  have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have ht0 : (0 : ℝ) < t := by exact_mod_cast ht
  have hlog : 0 ≤ log (t : ℝ) := log_nonneg ht1
  have hpow30 : (1 : ℝ) ≤ (t : ℝ)^30 := one_le_pow₀ ht1
  have hpow31 : (1 : ℝ) ≤ (t : ℝ)^31 := one_le_pow₀ ht1
  have hsmall : log (1+(t^31 : ℕ)/(199/200 : ℝ)) ≤ 3+31*log (t : ℝ) := by
    have hl := log_le_log (by positivity : (0 : ℝ) < 1+(t^31 : ℕ)/(199/200 : ℝ))
      (show 1+(t^31 : ℕ)/(199/200 : ℝ) ≤ 3*(t : ℝ)^31 by push_cast; nlinarith only [hpow31])
    rw [log_mul (by norm_num : (3 : ℝ) ≠ 0) (pow_ne_zero _ ht0.ne'), log_pow] at hl
    have h3 := log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
    norm_num only [Nat.cast_ofNat] at hl
    linarith
  have hcount : (S.card : ℝ)+1 ≤ ((D : ℝ)+2)*(t : ℝ)^30 := by
    have hc : (S.card : ℝ) ≤ (D : ℝ)*(t : ℝ)^30+1 := by exact_mod_cast hScard
    nlinarith
  have hmain := log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 199/200)
  have hmain' : log (199/200 : ℝ) ≤ -1/200 := by norm_num at hmain ⊢; linarith
  have hover : (S.card : ℝ)*log (1+(t^31 : ℕ)/(199/200 : ℝ))+1+log (t^31 : ℕ)/2 ≤
      (t : ℝ)^31/400 := by
    have h1 := mul_le_mul_of_nonneg_left hsmall (Nat.cast_nonneg S.card)
    have h2 := mul_le_mul_of_nonneg_right hcount (show 0 ≤ 3+31*log (t : ℝ) by positivity)
    have h3 := mul_le_mul_of_nonneg_right hcost (show 0 ≤ (t : ℝ)^30 by positivity)
    rw [Nat.cast_pow, log_pow] 
    norm_num only [Nat.cast_ofNat]
    have he : ((t : ℝ)/400)*(t : ℝ)^30 = (t : ℝ)^31/400 := by ring
    push_cast at h1
    rw [he] at h3
    nlinarith only [h1,h2,h3,hlog]
  have hneg := mul_le_mul_of_nonneg_left hmain' (show 0 ≤ (t : ℝ)^31 by positivity)
  apply hh.trans
  apply exp_le_exp.mpr
  push_cast at hover ⊢
  linarith only [hover,hneg]

/-- Uniform stretched-exponential decay at the actual prime budget itself,
not only at a quadratic interval length. -/
theorem eventually_linear_stretched_void_of_constants (D B : ℕ)
    (hD : 1024 ≤ D)
    (hlogD : 2048*(WeightedMertens.boundConstant+1) ≤ log (D : ℝ))
    (hB : fiveHalvesConstant*2^160 ≤ B) :
    ∀ᶠ k : ℕ in atTop, ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → P.card ≤ k →
      coveredFraction P k ≤ exp (-((k : ℝ)^(31/80 : ℝ)/400)) := by
  obtain ⟨N,hN⟩ := eventually_atTop.mp (eventually_linear_core_overhead D)
  let T := max (max N B) 1
  filter_upwards [eventually_ge_atTop (T^80)] with k hk
  intro P hP hPk
  have hT : 0 < T := by dsimp [T]; omega
  have hkpos : 0 < k := (Nat.pow_pos hT).trans_le hk
  obtain ⟨t,ht,hkt,hroot,htk⟩ := SoftExposure.exists_power_envelope k 80 hkpos (by omega)
  have hTt : T ≤ t := (Nat.pow_le_pow_iff_left (by omega : 80 ≠ 0)).mp (hk.trans hkt)
  have hNt : N ≤ t := (le_max_left N _).trans ((le_max_left _ _).trans hTt)
  have hlarge : fiveHalvesConstant*2^160 ≤ t := hB.trans ((le_max_right N _).trans ((le_max_left _ _).trans hTt))
  have hh := linear_core_envelope P hP k t D ht (hPk.trans hkt) hD hlogD
    (hN t hNt) (linear_exposure_budget k t ht hroot hlarge)
  have hp : (k : ℝ)^(31/80 : ℝ) ≤ (t : ℝ)^31 := by
    have he := rpow_le_rpow (Nat.cast_nonneg k) (show (k : ℝ) ≤ (t : ℝ)^80 by exact_mod_cast hkt)
      (by norm_num : (0 : ℝ) ≤ 31/80)
    rw [← rpow_natCast (t : ℝ) 80, ← rpow_mul (Nat.cast_nonneg t)] at he
    norm_num at he ⊢
    exact he
  exact hh.trans (exp_le_exp.mpr (by linarith only [hp]))

theorem eventually_linear_stretched_void :
    ∀ᶠ k : ℕ in atTop, ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → P.card ≤ k →
      coveredFraction P k ≤ exp (-((k : ℝ)^(31/80 : ℝ)/400)) :=
  eventually_linear_stretched_void_of_constants FiniteSelberg.thirteenSixteenthCutoffScale
    (fiveHalvesConstant*2^160)
    ((by norm_num : 1024 ≤ 65536).trans FiniteSelberg.thirteenSixteenthCutoffScale_ge)
    exposureCutoffScale_log le_rfl

#print axioms eventually_linear_stretched_void
end Erdos970.GapAverages
