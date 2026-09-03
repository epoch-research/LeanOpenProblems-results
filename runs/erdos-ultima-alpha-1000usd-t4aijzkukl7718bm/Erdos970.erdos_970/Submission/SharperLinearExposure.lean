import Submission.BuchstabSmoothGrowth
import Submission.LinearExposureTail

/-! A sharper unconditional linear-length void exponent, using the already
verified unrestricted smooth Buchstab bound. This is not a worst-case
quadratic bound. -/
namespace Erdos970.GapAverages
open Finset Real Filter
set_option maxHeartbeats 1000000

lemma smooth_power_envelope_bound (C : ℝ) (hC : 0 < C)
    (hbound : ∀ k : ℕ, 0 < k → (jacobsthalFunction k : ℝ) ≤
      C*(k : ℝ)^(51/25 : ℝ)*log ((k : ℝ)+2)^(26/25 : ℝ))
    (t : ℕ) (ht : 0 < t) :
    (jacobsthalFunction (t^37) : ℝ) ≤ 1600*C*(t : ℝ)^78 := by
  have ht0 : (0 : ℝ) < t := by exact_mod_cast ht
  have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have hp : ((t^37 : ℕ) : ℝ)^(51/25 : ℝ) ≤ (t : ℝ)^76 := by
    rw [Nat.cast_pow, ← rpow_natCast (t : ℝ) 37, ← rpow_mul ht0.le]
    norm_num only [Nat.cast_ofNat]
    have hh := rpow_le_rpow_of_exponent_le ht1 (by norm_num : (37 : ℝ)*(51/25) ≤ 76)
    simpa only [rpow_ofNat, show (37 : ℝ)*(51/25)=1887/25 by norm_num] using hh
  have ht37 : (1 : ℝ) ≤ (t : ℝ)^37 := one_le_pow₀ ht1
  have hl0 : 0 ≤ log ((t^37 : ℕ)+2 : ℝ) := log_nonneg (by push_cast; linarith only [ht37])
  have hl : log ((t^37 : ℕ)+2 : ℝ) ≤ 40*(t : ℝ) := by
    have hh := log_le_log (by positivity : (0 : ℝ) < ((t^37 : ℕ) : ℝ)+2)
      (show ((t^37 : ℕ) : ℝ)+2 ≤ 3*(t : ℝ)^37 by push_cast; linarith only [ht37])
    rw [log_mul (by norm_num : (3 : ℝ) ≠ 0) (pow_ne_zero _ ht0.ne'), log_pow] at hh
    have h3 := log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
    have hT := log_le_sub_one_of_pos ht0
    norm_num only [Nat.cast_ofNat] at hh
    linarith
  have hlp : log ((t^37 : ℕ)+2 : ℝ)^(26/25 : ℝ) ≤ (40*(t : ℝ))^2 := by
    apply (rpow_le_rpow hl0 hl (by norm_num : (0 : ℝ) ≤ 26/25)).trans
    have hh := rpow_le_rpow_of_exponent_le (by linarith : (1 : ℝ) ≤ 40*t)
      (by norm_num : (26/25 : ℝ) ≤ 2)
    simpa only [rpow_two] using hh
  have hh := hbound (t^37) (by positivity)
  have hu := mul_le_mul (mul_le_mul_of_nonneg_left hp hC.le) hlp (by positivity)
    (by positivity : 0 ≤ C*(t : ℝ)^76)
  apply hh.trans
  convert hu using 1 <;> ring

lemma sharper_linear_exposure_budget (C : ℝ) (hC : 0 < C)
    (hbound : ∀ k : ℕ, 0 < k → (jacobsthalFunction k : ℝ) ≤
      C*(k : ℝ)^(51/25 : ℝ)*log ((k : ℝ)+2)^(26/25 : ℝ))
    (k t : ℕ) (ht : 0 < t) (hroot : t^80 ≤ 2^80*k)
    (hlarge : 1600*C*(2 : ℝ)^80 ≤ t) : IsJacobsthalBound (t^37-1) k := by
  have hj := smooth_power_envelope_bound C hC hbound t ht
  have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have hpow : (t : ℝ)^79 ≤ (t : ℝ)^80 := pow_le_pow_right₀ ht1 (by omega)
  have hr : (t : ℝ)^80 ≤ (2 : ℝ)^80*k := by exact_mod_cast hroot
  have hs := mul_le_mul_of_nonneg_right hj (show (0 : ℝ) ≤ 2^80 by positivity)
  have hl := mul_le_mul_of_nonneg_right hlarge (show (0 : ℝ) ≤ (t : ℝ)^78 by positivity)
  have hh : (jacobsthalFunction (t^37) : ℝ) ≤ k := by
    have he : (t : ℝ)*(t : ℝ)^78 = (t : ℝ)^79 := by ring
    rw [he] at hl
    nlinarith only [hs,hl,hpow,hr]
  have hb := (jacobsthalFunction_le_iff (t^37) k).mp (by exact_mod_cast hh)
  intro n hn hnk a
  exact hb n hn (hnk.trans (Nat.sub_le _ _)) a

lemma sharper_core_cost (D t : ℕ) (ht : 0 < t) (hlarge : 15200*(D+2) ≤ t) :
    ((D : ℝ)+2)*(3+37*log t) ≤ (t : ℝ)^7/400 := by
  have ht0 : (0 : ℝ) < t := by exact_mod_cast ht
  have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have hlog := log_le_sub_one_of_pos ht0
  have hl : (15200 : ℝ)*((D : ℝ)+2) ≤ t := by exact_mod_cast hlarge
  have hp : (t : ℝ)^2 ≤ (t : ℝ)^7 := pow_le_pow_right₀ ht1 (by omega)
  have hh := mul_le_mul_of_nonneg_left (show 3+37*log (t : ℝ) ≤ 38*t by linarith)
    (show 0 ≤ (D : ℝ)+2 by positivity)
  have hs := mul_le_mul_of_nonneg_right hl ht0.le
  nlinarith only [hh,hs,hp]

lemma sharper_linear_core_envelope (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (k t D : ℕ) (ht : 0 < t) (hcard : P.card ≤ t^80)
    (hD : 1024 ≤ D) (hlogD : 2048*(WeightedMertens.boundConstant+1) ≤ log (D : ℝ))
    (hcost : ((D : ℝ)+2)*(3+37*log t) ≤ (t : ℝ)^7/400)
    (hb : IsJacobsthalBound (t^37-1) k) :
    coveredFraction P k ≤ exp (-(t : ℝ)^37/400) := by
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
  have hh := coveredFraction_le_general_core P S hP hSP k (t^37) (by positivity)
    hb (199/200) (by norm_num) htail
  have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have ht0 : (0 : ℝ) < t := by exact_mod_cast ht
  have hlog : 0 ≤ log (t : ℝ) := log_nonneg ht1
  have hpow30 : (1 : ℝ) ≤ (t : ℝ)^30 := one_le_pow₀ ht1
  have hpow37 : (1 : ℝ) ≤ (t : ℝ)^37 := one_le_pow₀ ht1
  have hsmall : log (1+(t^37 : ℕ)/(199/200 : ℝ)) ≤ 3+37*log (t : ℝ) := by
    have hl := log_le_log (by positivity : (0 : ℝ) < 1+(t^37 : ℕ)/(199/200 : ℝ))
      (show 1+(t^37 : ℕ)/(199/200 : ℝ) ≤ 3*(t : ℝ)^37 by push_cast; nlinarith only [hpow37])
    rw [log_mul (by norm_num : (3 : ℝ) ≠ 0) (pow_ne_zero _ ht0.ne'), log_pow] at hl
    have h3 := log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
    norm_num only [Nat.cast_ofNat] at hl
    linarith
  have hcount : (S.card : ℝ)+1 ≤ ((D : ℝ)+2)*(t : ℝ)^30 := by
    have hc : (S.card : ℝ) ≤ (D : ℝ)*(t : ℝ)^30+1 := by exact_mod_cast hScard
    nlinarith
  have hmain := log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 199/200)
  have hmain' : log (199/200 : ℝ) ≤ -1/200 := by norm_num at hmain ⊢; linarith
  have hover : (S.card : ℝ)*log (1+(t^37 : ℕ)/(199/200 : ℝ))+1+log (t^37 : ℕ)/2 ≤
      (t : ℝ)^37/400 := by
    have h1 := mul_le_mul_of_nonneg_left hsmall (Nat.cast_nonneg S.card)
    have h2 := mul_le_mul_of_nonneg_right hcount (show 0 ≤ 3+37*log (t : ℝ) by positivity)
    have h3 := mul_le_mul_of_nonneg_right hcost (show 0 ≤ (t : ℝ)^30 by positivity)
    rw [Nat.cast_pow, log_pow] 
    norm_num only [Nat.cast_ofNat]
    have he : ((t : ℝ)^7/400)*(t : ℝ)^30 = (t : ℝ)^37/400 := by ring
    push_cast at h1
    rw [he] at h3
    nlinarith only [h1,h2,h3,hlog]
  have hneg := mul_le_mul_of_nonneg_left hmain' (show 0 ≤ (t : ℝ)^37 by positivity)
  apply hh.trans
  apply exp_le_exp.mpr
  push_cast at hover ⊢
  linarith only [hover,hneg]


theorem eventually_sharper_linear_void_of_constants (D B : ℕ) (C : ℝ) (hC : 0 < C)
    (hbound : ∀ k : ℕ, 0 < k → (jacobsthalFunction k : ℝ) ≤
      C*(k : ℝ)^(51/25 : ℝ)*log ((k : ℝ)+2)^(26/25 : ℝ))
    (hD : 1024 ≤ D) (hlogD : 2048*(WeightedMertens.boundConstant+1) ≤ log (D : ℝ))
    (hB : 1600*C*(2 : ℝ)^80 ≤ B) :
    ∀ᶠ k : ℕ in atTop, ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → P.card ≤ k →
      coveredFraction P k ≤ exp (-((k : ℝ)^(37/80 : ℝ)/400)) := by
  let T := max (max (15200*(D+2)) B) 1
  filter_upwards [eventually_ge_atTop (T^80)] with k hk
  intro P hP hPk
  have hT : 0 < T := by dsimp [T]; omega
  have hkpos : 0 < k := (Nat.pow_pos hT).trans_le hk
  obtain ⟨t,ht,hkt,hroot,htk⟩ := SoftExposure.exists_power_envelope k 80 hkpos (by omega)
  have hTt : T ≤ t := (Nat.pow_le_pow_iff_left (by omega : 80 ≠ 0)).mp (hk.trans hkt)
  have hDt : 15200*(D+2) ≤ t := (le_max_left _ _).trans ((le_max_left _ _).trans hTt)
  have hBt : B ≤ t := (le_max_right _ _).trans ((le_max_left _ _).trans hTt)
  have hlarge : 1600*C*(2 : ℝ)^80 ≤ t := hB.trans (by exact_mod_cast hBt)
  have hh := sharper_linear_core_envelope P hP k t D ht (hPk.trans hkt) hD hlogD
    (sharper_core_cost D t ht hDt) (sharper_linear_exposure_budget C hC hbound k t ht hroot hlarge)
  have hp : (k : ℝ)^(37/80 : ℝ) ≤ (t : ℝ)^37 := by
    have he := rpow_le_rpow (Nat.cast_nonneg k) (show (k : ℝ) ≤ (t : ℝ)^80 by exact_mod_cast hkt)
      (by norm_num : (0 : ℝ) ≤ 37/80)
    rw [← rpow_natCast (t : ℝ) 80, ← rpow_mul (Nat.cast_nonneg t)] at he
    norm_num at he ⊢
    exact he
  exact hh.trans (exp_le_exp.mpr (by linarith only [hp]))

/-- An unconditional linear-length void exponent strictly greater than 2/5. -/
theorem eventually_sharper_linear_stretched_void :
    ∀ᶠ k : ℕ in atTop, ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → P.card ≤ k →
      coveredFraction P k ≤ exp (-((k : ℝ)^(37/80 : ℝ)/400)) := by
  obtain ⟨C,hC,hbound⟩ := RecursiveSieve.Buchstab.exists_smoothBuchstab_bound
  obtain ⟨B,hB⟩ := exists_nat_gt (1600*C*(2 : ℝ)^80)
  exact eventually_sharper_linear_void_of_constants FiniteSelberg.thirteenSixteenthCutoffScale
    B C hC hbound
    ((by norm_num : 1024 ≤ 65536).trans FiniteSelberg.thirteenSixteenthCutoffScale_ge)
    exposureCutoffScale_log hB.le

#print axioms eventually_sharper_linear_stretched_void
end Erdos970.GapAverages
