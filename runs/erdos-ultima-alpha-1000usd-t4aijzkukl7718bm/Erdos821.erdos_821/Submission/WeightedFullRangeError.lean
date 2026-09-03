import Submission.OddIntervalDivisorMoments

/-!
# Full-range absolute errors at the natural higher-divisor scale

The odd-modulus obstruction remains of size X*(log X)^k at divisor order
k+1. Constants and scale thresholds may depend on the fixed order. This is
not an obstruction to signed cancellation or to shorter modulus ranges.
-/

open Nat Filter ArithmeticFunction
open scoped Classical BigOperators ArithmeticFunction.zeta Topology

namespace Erdos821.FullRangeError

open AnalyticSieve HigherDivisors
set_option maxHeartbeats 2000000

lemma weighted_main_minus_actual_le_error (k : ℕ) (P : Finset ℕ) (X : ℕ)
    (hP : P ⊆ Finset.Icc 1 X) :
    mangoldtSum X/(X : ℝ) * (∑ d ∈ P, (tau k d : ℝ)) -
      (∑ d ∈ P, (tau k d : ℝ)*residueOneMangoldt d X) ≤ divisorProgressionError k X X := by
  have hmain : mangoldtSum X/(X : ℝ) * (∑ d ∈ P, (tau k d : ℝ)) ≤
      ∑ d ∈ P, (tau k d : ℝ)*(mangoldtSum X/(d.totient : ℝ)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro d hd
    obtain ⟨hd1, hdX⟩ := Finset.mem_Icc.mp (hP hd)
    have hφ : (0 : ℝ) < d.totient := by exact_mod_cast Nat.totient_pos.mpr hd1
    have hφX : (d.totient : ℝ) ≤ X := by exact_mod_cast (Nat.totient_le d).trans hdX
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_left (mangoldtSum_nonneg X) hφ hφX) (Nat.cast_nonneg _)
  have herror : (∑ d ∈ P, (tau k d : ℝ)*(mangoldtSum X/(d.totient : ℝ))) -
      (∑ d ∈ P, (tau k d : ℝ)*residueOneMangoldt d X) ≤ divisorProgressionError k X X := by
    rw [← Finset.sum_sub_distrib]
    apply le_trans (Finset.sum_le_sum (fun d _ => ?_))
      (Finset.sum_le_sum_of_subset_of_nonneg hP (fun d hd hdP => by positivity))
    rw [← mul_sub]
    exact mul_le_mul_of_nonneg_left
      (by simpa only [neg_sub] using
        neg_le_abs (residueOneMangoldt d X - mangoldtSum X/(d.totient : ℝ))) (Nat.cast_nonneg _)
  linarith

lemma weighted_large_odd_progression_sum_le (k : ℕ) (P : Finset ℕ) (X : ℕ) (B : ℝ)
    (hB : 0 ≤ B) (hweight : ∀ d ∈ P, (tau k d : ℝ) ≤ B)
    (hP : ∀ d ∈ P, 0 < d ∧ d < X ∧ X ≤ 2*d ∧ ¬(d+1).Coprime 2) :
    (∑ d ∈ P, (tau k d : ℝ)*residueOneMangoldt d X) ≤ B*characterLiftError 2 X := by
  calc
    _ ≤ ∑ d ∈ P, B*residueOneMangoldt d X := by
      apply Finset.sum_le_sum
      intro d hd
      apply mul_le_mul_of_nonneg_right (hweight d hd)
      exact Finset.sum_nonneg (fun n hn => by split_ifs <;> first | exact vonMangoldt_nonneg | exact le_rfl)
    _ = B * ∑ d ∈ P, residueOneMangoldt d X := (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (large_odd_progression_sum_le P X hP) hB

lemma weighted_full_error_lower (k N T : ℕ) (hN : 0 < N) (hNT : 2*T ≤ N)
    (B : ℝ) (hB : 0 ≤ B) (hweight : ∀ d ∈ oddLargeModuli N, (tau (k+1) d : ℝ) ≤ B) :
    mangoldtSum (4*N)/16 * oddHarmonicMoment k T - B*characterLiftError 2 (4*N) ≤
      divisorProgressionError (k+1) (4*N) (4*N) := by
  have hP := oddLargeModuli_properties N
  have he := weighted_main_minus_actual_le_error (k+1) (oddLargeModuli N) (4*N)
    (fun d hd => Finset.mem_Icc.mpr ⟨(hP d hd).1, (hP d hd).2.1.le⟩)
  have ha := weighted_large_odd_progression_sum_le (k+1) (oddLargeModuli N) (4*N) B hB hweight hP
  have hmain := mul_le_mul_of_nonneg_left (odd_interval_divisor_weight_lower k N T hNT)
    (div_nonneg (mangoldtSum_nonneg (4*N)) (Nat.cast_nonneg (4*N)))
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hid : mangoldtSum (4*N)/((4*N : ℕ) : ℝ) * ((N : ℝ)*oddHarmonicMoment k T/4) =
      mangoldtSum (4*N)/16 * oddHarmonicMoment k T := by
    push_cast
    field_simp
    ring
  rw [hid] at hmain
  linarith

lemma progressionScale_small_rpow (s : ℕ) :
    (progressionScaleN s : ℝ)^(1/64 : ℝ) = (2 : ℝ)^s := by
  unfold progressionScaleN
  rw [Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast_mul (by norm_num)]
  have he : ((64*s : ℕ) : ℝ)*(1/64) = (s : ℝ) := by push_cast; ring
  rw [he, Real.rpow_natCast]

lemma exists_progression_divisor_weight_bound (k : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ s n : ℕ, n ≤ progressionScaleN s →
      (tau (k+1) n : ℝ) ≤ C*(2 : ℝ)^s := by
  obtain ⟨C, hC, hweight⟩ := tau_succ_le_const_mul_rpow k (1/64) (by norm_num)
  refine ⟨C, hC, ?_⟩
  intro s n hn
  calc
    _ ≤ C*(n : ℝ)^(1/64 : ℝ) := hweight n
    _ ≤ C*(progressionScaleN s : ℝ)^(1/64 : ℝ) :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hn) (by norm_num)) (by linarith)
    _ = _ := by rw [progressionScale_small_rpow]

lemma eventually_weighted_liftError_le (C c : ℝ) (hC : 0 ≤ C) (hc : 0 < c) :
    ∀ᶠ s : ℕ in atTop, (C*(2 : ℝ)^s)*characterLiftError 2 (progressionScaleN s) ≤
      c*(progressionScaleN s : ℝ) := by
  let D : ℕ := ⌈64*C/c⌉₊
  have hD : 64*C ≤ c*(D : ℝ) := by
    have h := Nat.le_ceil (64*C/c)
    exact (div_le_iff₀ hc).mp h |>.trans_eq (mul_comm _ _)
  filter_upwards [eventually_nat_poly_le_two_pow 1 D 1] with s hs
  have hsR : (D : ℝ)*((s : ℝ)+1) ≤ (2 : ℝ)^s := by
    exact_mod_cast (by simpa only [one_mul, pow_one] using hs)
  have hcoef : 64*C*(s : ℝ) ≤ c*(2 : ℝ)^s := by
    have h1 := mul_le_mul_of_nonneg_right hD (Nat.cast_nonneg (α := ℝ) s)
    have h2 := mul_le_mul_of_nonneg_left hsR hc.le
    have h3 : 0 ≤ c*(D : ℝ) := by positivity
    nlinarith only [h1, h2, h3]
  have hlog : Real.log 2 ≤ 1 := by
    simpa only [show (2 : ℝ)-1 = 1 by norm_num] using
      Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  have hlift : characterLiftError 2 (progressionScaleN s) ≤ 64*(s : ℝ) := by
    simp only [characterLiftError, progressionScaleN, Nat.log_pow (by decide : 1 < 2), Nat.cast_mul]
    norm_num
    exact mul_le_of_le_one_right (by positivity) hlog
  have hpow : ((2 : ℝ)^s)^2 ≤ (progressionScaleN s : ℝ) := by
    simp only [progressionScaleN, Nat.cast_pow, Nat.cast_ofNat, ← pow_mul]
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  calc
    _ ≤ (C*(2 : ℝ)^s)*(64*(s : ℝ)) := mul_le_mul_of_nonneg_left hlift (by positivity)
    _ = (64*C*(s : ℝ))*(2 : ℝ)^s := by ring
    _ ≤ (c*(2 : ℝ)^s)*(2 : ℝ)^s := mul_le_mul_of_nonneg_right hcoef (by positivity)
    _ = c*((2 : ℝ)^s)^2 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hpow hc.le

lemma odd_root_harmonic_lower (k s : ℕ) :
    (s : ℝ)^k/((2 : ℝ)^k*(k.factorial : ℝ)) ≤ oddHarmonicMoment k (2^(32*s)) := by
  have hlog : (s : ℝ) ≤ Real.log ((2^(32*s) : ℕ)+1 : ℝ) := by
    have hbase : (s : ℝ) ≤ Real.log ((2^(32*s) : ℕ) : ℝ) := by
      simp only [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow, Nat.cast_mul]
      nlinarith [Real.log_two_gt_d9, Nat.cast_nonneg (α := ℝ) s]
    exact hbase.trans (Real.log_le_log (by positivity) (by push_cast; linarith))
  apply le_trans _ (oddHarmonicMoment_factorial_lower k (2^(32*s)) (one_le_pow₀ (by norm_num)))
  exact div_le_div_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg _) hlog k) (by positivity)

/-- A fixed-order positive proportion of the natural logarithmic scale
is forced into the FULL-RANGE absolute discrepancy. -/
theorem exists_weighted_full_error_scale_lower (k : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ s : ℕ in atTop,
      c*(progressionScaleN s : ℝ)*(s : ℝ)^k ≤
        divisorProgressionError (k+1) (progressionScaleN s) (progressionScaleN s) := by
  obtain ⟨C, hC, hweight⟩ := exists_progression_divisor_weight_bound k
  let c0 : ℝ := 1/(128*(2 : ℝ)^k*(k.factorial : ℝ))
  have hc0 : 0 < c0 := by dsimp [c0]; positivity
  refine ⟨c0/2, by positivity, ?_⟩
  filter_upwards [eventually_weighted_liftError_le C (c0/2) (by linarith) (by positivity),
    eventually_ge_atTop 1] with s hrem hs
  let N := 2^(64*s-2)
  let T := 2^(32*s)
  have hN : 0 < N := by dsimp [N]; positivity
  have hX : 4*N = progressionScaleN s := by
    dsimp [N, progressionScaleN]
    rw [show (4 : ℕ) = 2^2 by norm_num, ← pow_add]
    congr 1
    omega
  have hNT : 2*T ≤ N := by
    dsimp [N, T]
    rw [← _root_.pow_succ']
    apply Nat.pow_le_pow_right (by norm_num)
    omega
  have he := weighted_full_error_lower k N T hN hNT (C*(2 : ℝ)^s) (by positivity)
    (fun d hd => hweight s d (by
      have h := (oddLargeModuli_properties N d hd).2.1
      omega))
  rw [hX] at he
  have hH := odd_root_harmonic_lower k s
  change (s : ℝ)^k/((2 : ℝ)^k*(k.factorial : ℝ)) ≤ oddHarmonicMoment k T at hH
  have hψ := progression_scale_mangoldt_lower hs
  have hmain : c0*(progressionScaleN s : ℝ)*(s : ℝ)^k ≤
      mangoldtSum (progressionScaleN s)/16 * oddHarmonicMoment k T := by
    have h := mul_le_mul hψ hH (by positivity)
      (mangoldtSum_nonneg (progressionScaleN s))
    have h' := div_le_div_of_nonneg_right h (show (0 : ℝ) ≤ 16 by norm_num)
    convert h' using 1 <;> dsimp [c0] <;> ring
  have hsR : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hlarge : c0*(progressionScaleN s : ℝ) ≤ c0*(progressionScaleN s : ℝ)*(s : ℝ)^k :=
    le_mul_of_one_le_right (by positivity) (one_le_pow₀ hsR)
  linarith

/-- The same obstruction expressed at X*(log X)^k, for each fixed order.
No assertion about signed errors or X^theta cutoffs is made. -/
theorem exists_weighted_full_error_log_lower (k : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ s : ℕ in atTop,
      c*(progressionScaleN s : ℝ)*(Real.log (progressionScaleN s))^k ≤
        divisorProgressionError (k+1) (progressionScaleN s) (progressionScaleN s) := by
  obtain ⟨c, hc, h⟩ := exists_weighted_full_error_scale_lower k
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨c/(64*Real.log 2)^k, by positivity, ?_⟩
  filter_upwards [h] with s hs
  have he : Real.log (progressionScaleN s) = (64*Real.log 2)*(s : ℝ) := by
    simp only [progressionScaleN, Nat.cast_pow, Nat.cast_ofNat, Real.log_pow, Nat.cast_mul]
    ring
  rw [he, mul_pow]
  have hden : (64*Real.log 2)^k ≠ 0 := by positivity
  convert hs using 1
  field_simp
  ring

theorem not_full_error_littleO_divisor_scale (k : ℕ) :
    ¬(fun s : ℕ => divisorProgressionError (k+1) (progressionScaleN s) (progressionScaleN s))
      =o[atTop] (fun s : ℕ => (progressionScaleN s : ℝ)*(Real.log (progressionScaleN s))^k) := by
  intro H
  obtain ⟨c, hc, hlo⟩ := exists_weighted_full_error_log_lower k
  have hhi := H.bound (show 0 < c/2 by positivity)
  have hfalse : ∀ᶠ s : ℕ in atTop, False := by
    filter_upwards [hlo, hhi, eventually_ge_atTop 1] with s hl hu hs
    have hsR : (0 : ℝ) < s := by exact_mod_cast hs
    have hlog : 0 < Real.log (progressionScaleN s) := by
      simp only [progressionScaleN, Nat.cast_pow, Nat.cast_ofNat, Real.log_pow, Nat.cast_mul]
      positivity [Real.log_pos (by norm_num : (1 : ℝ) < 2)]
    have hscale : 0 < (progressionScaleN s : ℝ)*(Real.log (progressionScaleN s))^k := by
      have hX : (0 : ℝ) < progressionScaleN s := by unfold progressionScaleN; positivity
      positivity
    simp only [Real.norm_eq_abs,
      abs_of_nonneg (divisorProgressionError_nonneg (k+1) (progressionScaleN s) (progressionScaleN s)),
      abs_of_nonneg hscale.le] at hu
    have hm : 0 < c*((progressionScaleN s : ℝ)*(Real.log (progressionScaleN s))^k) :=
      mul_pos hc hscale
    nlinarith only [hl, hu, hm]
  exact hfalse.exists.elim (fun _ h => h)

end Erdos821.FullRangeError
