import Submission.SmoothCutoffContinuity

/-!
# A strict cutoff refinement from any fixed positive single-log prime supply

The refinement has an explicit density cost. It is not a uniform iteration
to arbitrarily small smoothness ratios.
-/
open Nat Finset Filter ArithmeticFunction
open scoped Classical BigOperators Topology
namespace Erdos821
open AnalyticSieve HigherDivisors
set_option maxHeartbeats 3000000

lemma smoothPrimeLogMass_card_lower (N Y R : ℕ) (L : ℝ) (hL : 0 ≤ L)
    (hlarge : ∀ p ∈ smoothPrimePool N Y, R<p → L ≤ Real.log p) :
    L*((smoothPrimePool N Y).card : ℝ) ≤ smoothPrimeLogMass N Y+L*R := by
  have hc : ((smoothPrimePool N Y).filter (fun p => p ≤ R)).card ≤ R := by
    apply (card_le_card (show (smoothPrimePool N Y).filter (fun p => p ≤ R) ⊆ Icc 1 R by
      intro p hp
      obtain ⟨hp,hpR⟩ := mem_filter.mp hp
      have hpr := (Nat.mem_primesBelow.mp (mem_filter.mp hp).1).2
      exact mem_Icc.mpr ⟨hpr.pos,hpR⟩)).trans_eq
    simp
  calc
    _ = ∑ _p ∈ smoothPrimePool N Y, L := by simp only [sum_const,nsmul_eq_mul]; ring
    _ ≤ ∑ p ∈ smoothPrimePool N Y, (Real.log (p : ℝ)+(if p ≤ R then L else 0)) := by
      apply sum_le_sum
      intro p hp
      by_cases h : p ≤ R
      · rw [if_pos h]
        linarith [Real.log_natCast_nonneg p]
      · rw [if_neg h,add_zero]
        exact hlarge p hp (by omega)
    _ = smoothPrimeLogMass N Y+L*(((smoothPrimePool N Y).filter (fun p => p ≤ R)).card : ℝ) := by
      rw [sum_add_distrib,← sum_filter]
      simp only [smoothPrimeLogMass,sum_const,nsmul_eq_mul,mul_comm]
    _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left (by exact_mod_cast hc) hL)

lemma mangoldtSum_le_six_mul (N : ℕ) : mangoldtSum N ≤ 6*(N : ℝ) := by
  rw [mangoldtSum_eq_psi]
  have hh := Chebyshev.psi_le_const_mul_self (x := (N : ℝ)) (Nat.cast_nonneg N)
  have hlog : Real.log 4 ≤ 2 := by
    rw [show (4 : ℝ)=2^2 by norm_num,Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith [Real.log_two_lt_d9]
  exact hh.trans (mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg N))

lemma weighted_supply_of_single_log_count (t b C : ℕ) (ht : 2 ≤ t) (hC : 0<C)
    (H : ∀ᶠ m : ℕ in atTop, (independentN t m : ℝ) ≤ (C : ℝ)*m*
      ((smoothPrimePool (independentN t m) (independentN b m)).card : ℝ)) :
    ∀ᶠ m : ℕ in atTop, (1/(12*(C : ℝ)))*mangoldtSum (progressionScaleN (t*m)) ≤
      smoothPrimeLogMass (progressionScaleN (t*m)) (progressionScaleN (b*m)) := by
  have hCr : (0 : ℝ)<C := by exact_mod_cast hC
  filter_upwards [H,eventually_power_saving_le_divisor t 1 1 (2*C) (by omega) (by omega)] with m hcount herr
  let N := independentN t m
  let Y := independentN b m
  let R := independentN (t-1) m
  have hRlog : (m : ℝ) ≤ Real.log (R : ℝ) := by
    have hh := log_progression_scale_ge ((t-1)*m)
    have hm : m ≤ (t-1)*m := Nat.le_mul_of_pos_left m (by omega)
    have he : R=progressionScaleN ((t-1)*m) := by dsimp [R,independentN,progressionScaleN]; congr 1; ring
    rw [he]
    exact (show (m : ℝ) ≤ ((t-1)*m : ℕ) by exact_mod_cast hm).trans hh
  have hpoint := smoothPrimeLogMass_card_lower N Y R (m : ℝ) (Nat.cast_nonneg m) (by
    intro p _hp hRp
    apply hRlog.trans
    exact Real.log_le_log (by dsimp [R,independentN]; positivity)
      (by exact_mod_cast hRp.le))
  have hRpow : (R : ℝ) ≤ (2 : ℝ)^((64*t-1)*m) := by
    dsimp [R,independentN]
    rw [Nat.cast_pow,Nat.cast_ofNat]
    apply pow_le_pow_right₀ (by norm_num)
    have ht1 := Nat.sub_add_cancel (by omega : 1 ≤ t)
    have ht64 := Nat.sub_add_cancel (by omega : 1 ≤ 64*t)
    nlinarith only [congrArg (fun z : ℕ => z*m) ht1,congrArg (fun z : ℕ => z*m) ht64,Nat.zero_le m]
  have herr' : (m : ℝ)*R ≤ (N : ℝ)/(2*(C : ℝ)) := by
    apply le_trans _ (by simpa only [Nat.cast_one,one_mul,pow_one,Nat.cast_mul,Nat.cast_ofNat] using herr)
    exact mul_le_mul (by linarith : (m : ℝ) ≤ (m : ℝ)+1) hRpow (Nat.cast_nonneg R) (by positivity)
  have hcount' : (N : ℝ)/(C : ℝ) ≤ (m : ℝ)*((smoothPrimePool N Y).card : ℝ) := by
    apply (div_le_iff₀ hCr).mpr
    convert hcount using 1
    dsimp only [N,Y]
    ring
  have hpsi := mangoldtSum_le_six_mul N
  have hlow : (1/(12*(C : ℝ)))*mangoldtSum N ≤ smoothPrimeLogMass N Y := by
    have hscaled := mul_le_mul_of_nonneg_left hpsi (show (0 : ℝ) ≤ 1/(12*(C : ℝ)) by positivity)
    have he2 : (N : ℝ)/(2*(C : ℝ))=((N : ℝ)/(C : ℝ))/2 := by ring
    have he12 : (1/(12*(C : ℝ)))*(6*(N : ℝ))=((N : ℝ)/(C : ℝ))/2 := by ring
    rw [he2] at herr'
    rw [he12] at hscaled
    linarith only [hcount',hpoint,herr',hscaled]
  simpa only [N,Y,independentN,progressionScaleN,mul_assoc] using hlow

lemma single_log_count_of_weighted_supply (t b : ℕ) (ht : 1 ≤ t) (c : ℝ) (hc : 0<c)
    (H : ∀ᶠ m : ℕ in atTop, c*mangoldtSum (progressionScaleN (t*m)) ≤
      smoothPrimeLogMass (progressionScaleN (t*m)) (progressionScaleN (b*m))) :
    ∃ C : ℕ, 0<C ∧ ∀ᶠ m : ℕ in atTop,
      (independentN t m : ℝ) ≤ (C : ℝ)*m*
        ((smoothPrimePool (independentN t m) (independentN b m)).card : ℝ) := by
  obtain ⟨C,hC⟩ := exists_nat_gt (max 1 (128*(t : ℝ)/c))
  have hC1 : (1 : ℝ)<C := (le_max_left _ _).trans_lt hC
  have hCc : 128*(t : ℝ)<(C : ℝ)*c := (div_lt_iff₀ hc).mp ((le_max_right _ _).trans_lt hC)
  refine ⟨C,by exact_mod_cast (lt_trans (by norm_num : (0 : ℝ)<1) hC1),?_⟩
  filter_upwards [H,(progressionScaleN_mul_tendsto t ht).eventually eventually_mangoldt_nine_tenths]
    with m hm hpsi
  let N := independentN t m
  let Y := independentN b m
  have hne : N=progressionScaleN (t*m) := by dsimp [N,independentN,progressionScaleN]; congr 1; ring
  have hye : Y=progressionScaleN (b*m) := by dsimp [Y,independentN,progressionScaleN]; congr 1; ring
  rw [← hne,← hye] at hm
  rw [← hne] at hpsi
  have hN : (0 : ℝ)<N := by dsimp [N,independentN]; positivity
  have hlower : (N : ℝ)/2 ≤ mangoldtSum N := by linarith only [hpsi,hN]
  have hlog : Real.log (N : ℝ) ≤ 64*(t : ℝ)*m := by
    simpa only [N,independentN,Nat.cast_mul,Nat.cast_ofNat] using log_two_pow_le (64*t*m)
  have hh := (mul_le_mul_of_nonneg_left hlower hc.le).trans
    (hm.trans ((smoothPrimeLogMass_le_log_card N Y).trans
      (mul_le_mul_of_nonneg_right hlog (Nat.cast_nonneg _))))
  have hcard : 0 ≤ (m : ℝ)*((smoothPrimePool N Y).card : ℝ) := by positivity
  have hmul := mul_le_mul_of_nonneg_right hCc.le hcard
  change (N : ℝ) ≤ (C : ℝ)*m*((smoothPrimePool N Y).card : ℝ)
  nlinarith only [hh,hmul,hc]

/-- Any fixed positive supply below the half-level can be refined once
to a strictly smaller rational smoothness ratio. -/
theorem exists_smaller_cutoff_single_log_count (t b C : ℕ) (ht : 22 ≤ t) (hb : 1 ≤ b)
    (hlevel : 2*b+5 ≤ t) (hC : 0<C)
    (H : ∀ᶠ m : ℕ in atTop, (independentN t m : ℝ) ≤ (C : ℝ)*m*
      ((smoothPrimePool (independentN t m) (independentN b m)).card : ℝ)) :
    ∃ K C' : ℕ, 2 ≤ K ∧ 0<C' ∧
      (((b*K-1 : ℕ) : ℝ)/((t*K : ℕ) : ℝ) < (b : ℝ)/(t : ℝ)) ∧
      ∀ᶠ m : ℕ in atTop, (independentN (t*K) m : ℝ) ≤ (C' : ℝ)*m*
        ((smoothPrimePool (independentN (t*K) m) (independentN (b*K-1) m)).card : ℝ) := by
  have hc : (0 : ℝ)<1/(12*(C : ℝ)) := by positivity
  obtain ⟨K,hK,hratio,Hsmall⟩ := exists_strictly_smaller_weighted_cutoff b t hb ht hlevel
    (1/(12*(C : ℝ))) hc (weighted_supply_of_single_log_count t b C (by omega) hC H)
  obtain ⟨C',hC',HC'⟩ := single_log_count_of_weighted_supply (t*K) (b*K-1)
    (Nat.mul_pos (by omega) (by omega)) ((1/(12*(C : ℝ)))/2) (half_pos hc) Hsmall
  exact ⟨K,C',hK,hC',hratio,HC'⟩

/-- This strict improvement is relative to the specific supplied ratio;
it does not assert an improvement beyond the supremum of all supplied ratios. -/
theorem exists_larger_exponent_of_single_log_count (t b C : ℕ) (ht : 22 ≤ t) (hb : 1 ≤ b)
    (hlevel : 2*b+5 ≤ t) (hC : 0<C)
    (H : ∀ᶠ m : ℕ in atTop, (independentN t m : ℝ) ≤ (C : ℝ)*m*
      ((smoothPrimePool (independentN t m) (independentN b m)).card : ℝ)) :
    ∃ γ : ℝ, 1-(b : ℝ)/(t : ℝ)<γ ∧ {n : ℕ | (g n : ℝ) > (n : ℝ)^γ}.Infinite := by
  obtain ⟨K,C',hK,hC',hratio,Hsmall⟩ := exists_smaller_cutoff_single_log_count t b C ht hb hlevel hC H
  obtain ⟨γ,hlo,hhi⟩ := exists_between (show 1-(b : ℝ)/(t : ℝ)<1-((b*K-1 : ℕ) : ℝ)/((t*K : ℕ) : ℝ) by linarith)
  refine ⟨γ,hlo,infinite_g_gt_of_single_log_smooth_count (t*K) (b*K-1) C' ?_ Hsmall γ hhi⟩
  have hh := Nat.mul_lt_mul_of_pos_right (show b<t by omega) (show 0<K by omega)
  omega

end Erdos821
