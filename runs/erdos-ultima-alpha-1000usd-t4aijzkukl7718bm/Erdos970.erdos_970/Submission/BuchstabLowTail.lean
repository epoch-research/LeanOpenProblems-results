import Submission.BuchstabCountPower
import Submission.SoftQuadraticLowTail

/-! An improved unconditional sub-mean lower tail at quadratic length. Its
exponent19/20 is still below the entropy needed to exclude every phase. -/
namespace Erdos970.SoftExposure
open Finset Real Filter GapAverages FiniteSelberg
open RecursiveSieve.Buchstab
set_option maxHeartbeats 0

noncomputable def refinedCountDenominator (t : ℕ) : ℝ :=
  buchstabCountLogConstant*log (((2*t^76 : ℕ) : ℝ)+2)

lemma refinedCountDenominator_pos (t : ℕ) : 0 < refinedCountDenominator t := by
  apply mul_pos buchstabCountLogConstant_pos
  apply log_pos
  have hh := Nat.cast_nonneg (α := ℝ) (2*t^76)
  linarith

lemma partial_budget_power (t : ℕ) : ((2*t^76 : ℕ) : ℝ)^(40/19 : ℝ) ≤ 8*(t : ℝ)^160 := by
  push_cast
  rw [mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (pow_nonneg (Nat.cast_nonneg t) 76),
    ← rpow_natCast (t : ℝ) 76,← rpow_mul (Nat.cast_nonneg t)]
  norm_num only [Nat.cast_ofNat,show (76 : ℝ)*(40/19)=160 by norm_num,rpow_ofNat]
  have hh := rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
    (show (40/19 : ℝ) ≤ 3 by norm_num)
  norm_num only [rpow_ofNat,OfNat.ofNat,show (2 : ℝ)^3 = 8 by norm_num] at hh
  exact mul_le_mul_of_nonneg_right hh (pow_nonneg (Nat.cast_nonneg t) _)

/-- The partial-count input now comes from the actual refined sieve rather
than the old hard-cubic count bound. -/
lemma exists_refined_partial_count : ∃ N : ℕ, ∀ t : ℕ, N ≤ t → 0 < t →
    ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → ∀ m : ℕ, 8*(t : ℝ)^160 ≤ m →
      ∀ r : ℕ → ℕ, PartialLower (2*t^76) (range m) P r ((m : ℝ)/refinedCountDenominator t) := by
  obtain ⟨N,hN⟩ := eventually_atTop.mp (eventually_prime_count_power (40/19) (by norm_num))
  refine ⟨N,fun t hNt ht P hP m hm r Q hQP hQcard => ?_⟩
  have ht76 : t ≤ 2*t^76 := (Nat.le_self_pow (by norm_num : 76 ≠ 0) t).trans (by omega)
  have hh := hN (2*t^76) (hNt.trans ht76) Q (fun p hp => hP p (hQP hp)) hQcard.le r m
    ((partial_budget_power t).trans hm)
  exact hh

lemma refined_exposure_core_cost (D t b : ℕ) (ht : 0 < t)
    (hDt : 4096*(D+1) ≤ t) (hb : b ≤ D*t^50+1) :
    (b : ℝ)*log (1+4*(t : ℝ)^76) ≤ (t : ℝ)^76/32 := by
  have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have ht0 : (0 : ℝ) < t := by exact_mod_cast ht
  have h50 : (1 : ℝ) ≤ (t : ℝ)^50 := one_le_pow₀ ht1
  have h76 : (1 : ℝ) ≤ (t : ℝ)^76 := one_le_pow₀ ht1
  have hlog0 : 0 ≤ log (1+4*(t : ℝ)^76) := log_nonneg (by
    have hh : (0 : ℝ) ≤ (t : ℝ)^76 := by positivity
    linarith)
  have hlog : log (1+4*(t : ℝ)^76) ≤ 76*t := by
    have hh := log_le_log (by positivity : 0 < 1+4*(t : ℝ)^76)
      (show 1+4*(t : ℝ)^76 ≤ 5*(t : ℝ)^76 by nlinarith only [h76])
    rw [log_mul (by norm_num) (pow_ne_zero _ ht0.ne'),log_pow] at hh
    have h5 := log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 5)
    have hT := log_le_sub_one_of_pos ht0
    norm_num only [Nat.cast_ofNat] at hh
    linarith only [hh,h5,hT]
  have hbR : (b : ℝ) ≤ ((D : ℝ)+1)*(t : ℝ)^50 := by
    have hh : (b : ℝ) ≤ (D : ℝ)*(t : ℝ)^50+1 := by exact_mod_cast hb
    nlinarith only [hh,h50]
  have hDtR : 4096*((D : ℝ)+1) ≤ t := by exact_mod_cast hDt
  have hp52 : (t : ℝ)^52 ≤ (t : ℝ)^76 := pow_le_pow_right₀ ht1 (by omega)
  have hh := mul_le_mul_of_nonneg_right hDtR (pow_nonneg ht0.le 51)
  have hc := mul_le_mul hbR hlog hlog0 (by positivity)
  have h52 : 0 ≤ (t : ℝ)^52 := by positivity
  nlinarith only [hh,hc,hp52,h52]

lemma refined_lowCount_envelope (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (m t D : ℕ) (ht : 0 < t) (hcard : P.card ≤ t^80) (hD1024 : 1024 ≤ D)
    (hlogD : 2048*(WeightedMertens.boundConstant+1) ≤ log (D : ℝ))
    (hDt : 4096*(D+1) ≤ t)
    (hpartial : ∀ r : ℕ → ℕ, PartialLower (2*t^76) (range m) P r ((m : ℝ)/refinedCountDenominator t))
    (hmpos : 0 < m) (b : ℝ) (hb : 0 ≤ b)
    (hbA : b ≤ (m : ℝ)/refinedCountDenominator t/256) :
    lowCountFraction P m b ≤ exp (-(t : ℝ)^76/64) := by
  let S := P.filter (fun p => p ≤ D*t^50)
  have hSP : S ⊆ P := filter_subset _ _
  have hScard : S.card ≤ D*t^50+1 := by
    have hs : S ⊆ range (D*t^50+1) := by
      intro p hp
      exact mem_range.mpr (by have := (mem_filter.mp hp).2; omega)
    simpa only [card_range] using card_le_card hs
  have hhalf : (∑ p ∈ P \ S, (p : ℝ)⁻¹) ≤ 1/2 := by
    have he : P \ S = P.filter (fun p => D*t^50 < p) := by
      ext p
      simp only [S,Finset.mem_sdiff,mem_filter]
      by_cases hp : p ∈ P <;> simp only [hp,true_and,false_and,not_true_eq_false,not_false_eq_true,not_le]
    rw [he]
    have hh := WeightedMertens.tail_five_eighths P hP (t^5) D (by positivity) hD1024 hlogD
      (by simpa only [← pow_mul] using hcard)
    simpa only [← pow_mul,one_div] using hh
  have hA : 0 < (m : ℝ)/refinedCountDenominator t :=
    div_pos (by exact_mod_cast hmpos) (refinedCountDenominator_pos t)
  have hh := lowCountFraction_le_core_exponential P S hP hSP m (t^76) (by positivity)
    ((m : ℝ)/refinedCountDenominator t) b hA hb hbA
    (fun r => hpartial (phaseResidues P r)) hhalf
  have hc := refined_exposure_core_cost D t S.card ht hDt hScard
  apply hh.trans
  apply exp_le_exp.mpr
  push_cast
  linarith only [hc]

noncomputable def refinedLowCountLogConstant : ℝ := 20480*buchstabCountLogConstant

def refinedQuadraticScale : ℕ := 8*2^160

lemma refinedLowCountLogConstant_pos : 0 < refinedLowCountLogConstant :=
  mul_pos (by norm_num) buchstabCountLogConstant_pos

lemma refined_denominator_le_log (t k : ℕ) (ht : 0 < t) (htk : t ≤ k) :
    256*refinedCountDenominator t ≤ refinedLowCountLogConstant*log ((k : ℝ)+2) := by
  have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have ht0 : (0 : ℝ) < t := by exact_mod_cast ht
  have ht76 : (1 : ℝ) ≤ (t : ℝ)^76 := one_le_pow₀ ht1
  have hlog : log (((2*t^76 : ℕ) : ℝ)+2) ≤ log (4*(t : ℝ)^76) := by
    apply log_le_log (by positivity)
    push_cast
    nlinarith only [ht76]
  rw [log_mul (by norm_num) (pow_ne_zero _ ht0.ne'),log_pow,
    show (4 : ℝ)=2^2 by norm_num,log_pow] at hlog
  norm_num only [Nat.cast_ofNat] at hlog
  have hl2 : log (2 : ℝ) ≤ log ((k : ℝ)+2) := log_le_log (by norm_num) (by have hh := Nat.cast_nonneg (α := ℝ) k; linarith)
  have hltk : log (t : ℝ) ≤ log ((k : ℝ)+2) := by
    apply log_le_log ht0
    have hh : (t : ℝ) ≤ k := by exact_mod_cast htk
    linarith
  have hT : 0 ≤ log ((k : ℝ)+2) := log_natCast_nonneg (k+2) |>.trans_eq (by push_cast; rfl)
  have hh : log (((2*t^76 : ℕ) : ℝ)+2) ≤ 80*log ((k : ℝ)+2) := by linarith
  have hm := mul_le_mul_of_nonneg_left hh buchstabCountLogConstant_pos.le
  dsimp only [refinedCountDenominator,refinedLowCountLogConstant]
  nlinarith only [hm]

lemma refined_quadratic_budget (k t : ℕ) (hroot : t^80 ≤ 2^80*k) :
    8*(t : ℝ)^160 ≤ (refinedQuadraticScale*k^2 : ℕ) := by
  have hpow : t^160 ≤ 2^160*k^2 := by
    have hh := Nat.pow_le_pow_left hroot 2
    convert hh using 1 <;> ring
  have hh := Nat.mul_le_mul_left 8 hpow
  have he : 8*(2^160*k^2) = refinedQuadraticScale*k^2 := by unfold refinedQuadraticScale; ring
  rw [he] at hh
  exact_mod_cast hh

lemma root_nineteen_twentieths (k t : ℕ) (hkt : k ≤ t^80) :
    (k : ℝ)^(19/20 : ℝ) ≤ (t : ℝ)^76 := by
  have hh := rpow_le_rpow (Nat.cast_nonneg k) (show (k : ℝ) ≤ (t : ℝ)^80 by exact_mod_cast hkt)
    (by norm_num : (0 : ℝ) ≤ 19/20)
  rw [← rpow_natCast (t : ℝ) 80,← rpow_mul (Nat.cast_nonneg t)] at hh
  norm_num at hh ⊢
  exact hh

/-- An unconditional near-zero lower tail with exponent19/20 at one fixed
quadratic length. It does not exclude a single exceptional covering phase. -/
theorem eventually_refined_quadratic_low_tail :
    ∀ᶠ k : ℕ in atTop, ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → P.card ≤ k →
      lowCountFraction P (refinedQuadraticScale*k^2)
        ((refinedQuadraticScale*k^2 : ℕ)/(refinedLowCountLogConstant*log ((k : ℝ)+2))) ≤
          exp (-((k : ℝ)^(19/20 : ℝ)/64)) := by
  obtain ⟨N,hN⟩ := exists_refined_partial_count
  let D := thirteenSixteenthCutoffScale
  let T := max N (4096*(D+1))
  have hT : 0 < T := (by dsimp only [T]; positivity)
  filter_upwards [eventually_ge_atTop (T^80)] with k hk
  intro P hP hPk
  have hkpos : 0 < k := (Nat.pow_pos hT).trans_le hk
  obtain ⟨t,ht,hkt,hroot,htk⟩ := exists_power_envelope k 80 hkpos (by omega)
  have hTt : T ≤ t := (Nat.pow_le_pow_iff_left (by norm_num : (80 : ℕ) ≠ 0)).mp (hk.trans hkt)
  have hNt : N ≤ t := (le_max_left _ _).trans hTt
  have hDt : 4096*(D+1) ≤ t := (le_max_right _ _).trans hTt
  have hD1024 : 1024 ≤ D := (by norm_num : 1024 ≤ 65536).trans thirteenSixteenthCutoffScale_ge
  have hlogD : 2048*(WeightedMertens.boundConstant+1) ≤ log (D : ℝ) := exposureCutoffScale_log
  let m := refinedQuadraticScale*k^2
  have hmpos : 0 < m := by dsimp only [m,refinedQuadraticScale]; positivity
  have hscale : 8*(t : ℝ)^160 ≤ m := refined_quadratic_budget k t hroot
  have hb : 0 ≤ (m : ℝ)/(refinedLowCountLogConstant*log ((k : ℝ)+2)) := by
    have hlog : 0 < log ((k : ℝ)+2) := log_pos (by have := Nat.cast_nonneg (α := ℝ) k; linarith)
    exact div_nonneg (Nat.cast_nonneg m) (mul_pos refinedLowCountLogConstant_pos hlog).le
  have hbA : (m : ℝ)/(refinedLowCountLogConstant*log ((k : ℝ)+2)) ≤
      (m : ℝ)/refinedCountDenominator t/256 := by
    have hh := div_le_div_of_nonneg_left (Nat.cast_nonneg m)
      (show 0 < 256*refinedCountDenominator t by exact mul_pos (by norm_num) (refinedCountDenominator_pos t))
      (refined_denominator_le_log t k ht htk)
    convert hh using 1
    ring
  have hh := refined_lowCount_envelope P hP m t D ht (hPk.trans hkt) hD1024 hlogD hDt
    (hN t hNt ht P hP m hscale) hmpos _ hb hbA
  exact hh.trans (exp_le_exp.mpr (by linarith only [root_nineteen_twentieths k t hkt]))

#print axioms exists_refined_partial_count
#print axioms eventually_refined_quadratic_low_tail
end Erdos970.SoftExposure
