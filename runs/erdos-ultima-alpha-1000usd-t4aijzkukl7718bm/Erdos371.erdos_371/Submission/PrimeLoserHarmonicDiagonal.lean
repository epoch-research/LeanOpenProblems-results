import Submission.DyadicSeriesTools
import Submission.PrimeWinnerHarmonicFlux

/-! A summable prime-weighted diagonal for harmonic loser currents.
This is not a bound for their signed off-diagonal collisions. -/
namespace Erdos371
open Finset Filter Asymptotics
open scoped Topology
set_option autoImplicit false

lemma summable_exp_neg_rpow_nat (a c : ℝ) (ha : 0<a) (hc : 0<c) :
    Summable (fun k : ℕ => Real.exp (-c*(k+1 : ℝ)^a)) := by
  have hx : Tendsto (fun k : ℕ => (k+1 : ℝ)^a) atTop atTop :=
    (tendsto_rpow_atTop ha).comp ((tendsto_natCast_atTop_atTop (R := ℝ)).atTop_add (tendsto_const_nhds (x := (1 : ℝ))))
  have ho := (isLittleO_exp_neg_mul_rpow_atTop hc (-2/a)).comp_tendsto hx
  have he (k : ℕ) : ((k+1 : ℝ)^a)^(-2/a) = (k+1 : ℝ)^(-2 : ℝ) := by
    rw [← Real.rpow_mul (by positivity : (0 : ℝ)≤k+1)]
    congr 1
    field_simp
  simp only [Function.comp_def,he] at ho
  have hs : Summable (fun k : ℕ => (k+1 : ℝ)^(-2 : ℝ)) := by
    have h := (summable_nat_add_iff 1).mpr
      (Real.summable_nat_rpow.mpr (by norm_num : (-2 : ℝ)< -1))
    simpa only [Nat.cast_add,Nat.cast_one] using h
  exact summable_of_isBigO_nat hs ho.isBigO

lemma threeQuarter_threshold_ratio (k : ℕ) :
    ((2 : ℝ)^(k+1))^(1-threeQuarterBandWidth k)/(2 : ℝ)^k =
      2*Real.exp (-(Real.log 2/8)*(k+1 : ℝ)^(1/4 : ℝ)) := by
  have hb : (0 : ℝ)<(2 : ℝ)^(k+1) := by positivity
  have he : (k+1 : ℝ)*(k+1 : ℝ)^(-3/4 : ℝ) = (k+1 : ℝ)^(1/4 : ℝ) := by
    nth_rw 1 [← Real.rpow_one (k+1 : ℝ)]
    rw [← Real.rpow_add (by positivity : (0 : ℝ)<k+1)]
    norm_num
  rw [sub_eq_add_neg,Real.rpow_add hb,Real.rpow_one]
  rw [Real.rpow_def_of_pos hb,Real.log_pow]
  have hex : ((k+1 : ℕ) : ℝ)*Real.log 2*(-threeQuarterBandWidth k) =
      -(Real.log 2/8)*(k+1 : ℝ)^(1/4 : ℝ) := by
    unfold threeQuarterBandWidth
    push_cast
    rw [show (k+1 : ℝ)*Real.log 2*(-((1/8 : ℝ)*(k+1 : ℝ)^(-3/4 : ℝ))) =
      -(Real.log 2/8)*((k+1 : ℝ)*(k+1 : ℝ)^(-3/4 : ℝ)) by ring,he]
  rw [hex,pow_succ]
  field_simp

lemma summable_threeQuarter_threshold_ratio :
    Summable (fun k : ℕ =>
      ((2 : ℝ)^(k+1))^(1-threeQuarterBandWidth k)/(2 : ℝ)^k) := by
  simp_rw [threeQuarter_threshold_ratio]
  exact (summable_exp_neg_rpow_nat (1/4) (Real.log 2/8) (by norm_num)
    (div_pos (Real.log_pos (by norm_num)) (by norm_num))).mul_left 2

noncomputable def primeLoserHarmonicDiagonal (n : ℕ) : ℝ :=
  (primeLoser n : ℝ)/(n : ℝ)^2

lemma primeLoserHarmonicDiagonal_nonneg (n : ℕ) :
    0≤primeLoserHarmonicDiagonal n := by
  unfold primeLoserHarmonicDiagonal
  positivity

lemma primeLoserHarmonicDiagonal_block_bound (u : ℕ → ℝ) (k : ℕ) :
    (∑ n ∈ Ico (2^k) (2^(k+1)), primeLoserHarmonicDiagonal n) ≤
      ((2 : ℝ)^(k+1))^(1-u k)/(2 : ℝ)^k +
        ∑ n ∈ Ico (2^k) (2^(k+1)), dyadicTopPrimeReciprocal u n := by
  classical
  let T : ℝ := ((2 : ℝ)^(k+1))^(1-u k)
  have hL : (0 : ℝ)<(2 : ℝ)^k := by positivity
  have hT : 0≤T := by dsimp [T]; positivity
  have hterm (n : ℕ) (hn : n ∈ Ico (2^k) (2^(k+1))) :
      primeLoserHarmonicDiagonal n ≤ T/((2 : ℝ)^k)^2+dyadicTopPrimeReciprocal u n := by
    have hn' := mem_Ico.mp hn
    have hnL : (2 : ℝ)^k≤n := by exact_mod_cast hn'.1
    have hn0 : (0 : ℝ)<n := hL.trans_le hnL
    have hlog : Nat.log 2 n=k := Nat.log_eq_of_pow_le_of_lt_pow hn'.1 hn'.2
    have hiff : T<(primeLoser n : ℝ) ↔ dyadicTopPrimePair u n := by
      simp only [primeLoser,Nat.cast_min,lt_min_iff,dyadicTopPrimePair,hlog,T]
    by_cases h : dyadicTopPrimePair u n
    · rw [dyadicTopPrimeReciprocal,if_pos h]
      have hp : (primeLoser n : ℝ)≤n := by
        exact_mod_cast (min_le_left (Nat.maxPrimeFac n) (Nat.maxPrimeFac (n+1))).trans Nat.maxPrimeFac_le
      have hb : primeLoserHarmonicDiagonal n≤1/(n : ℝ) := by
        unfold primeLoserHarmonicDiagonal
        apply (div_le_iff₀ (pow_pos hn0 2)).mpr
        field_simp
        exact hp
      exact hb.trans (le_add_of_nonneg_left (div_nonneg hT (sq_nonneg _)))
    · rw [dyadicTopPrimeReciprocal,if_neg h,add_zero]
      have hp : (primeLoser n : ℝ)≤T := not_lt.mp (fun hh => h (hiff.mp hh))
      unfold primeLoserHarmonicDiagonal
      exact (div_le_div_of_nonneg_right hp (sq_nonneg _)).trans
        (div_le_div_of_nonneg_left hT (pow_pos hL 2) (pow_le_pow_left₀ hL.le hnL 2))
  have hh := sum_le_sum hterm
  rw [sum_add_distrib,sum_const,nsmul_eq_mul] at hh
  have hcard : (Ico (2^k) (2^(k+1))).card = (2 : ℕ)^k := by
    rw [Nat.card_Ico,pow_succ]
    omega
  rw [hcard,Nat.cast_pow,Nat.cast_ofNat] at hh
  convert hh using 1
  dsimp [T]
  field_simp

/-- The entire prime-weighted harmonic diagonal is summable. The square of
an accumulated current also has off-diagonal terms, not bounded here. -/
theorem summable_primeLoserHarmonicDiagonal : Summable primeLoserHarmonicDiagonal := by
  apply summable_of_nonneg_dyadic_blocks _ primeLoserHarmonicDiagonal_nonneg
  have hs := summable_dyadic_blocks_of_nonneg
    (dyadicTopPrimeReciprocal threeQuarterBandWidth)
    (dyadicTopPrimeReciprocal_nonneg threeQuarterBandWidth)
    summable_threeQuarter_top_prime_pairs
  exact Summable.of_nonneg_of_le
    (fun k => sum_nonneg (fun n _ => primeLoserHarmonicDiagonal_nonneg n))
    (primeLoserHarmonicDiagonal_block_bound threeQuarterBandWidth)
    (summable_threeQuarter_threshold_ratio.add hs)

/-- Exactly one loser label contributes to each squared-increment row. -/
lemma primeLoserHarmonicTerm_weighted_square_row (n : ℕ) :
    (∑' p : ℕ, (p : ℝ)*(primeLoserHarmonicTerm p n)^2) =
      primeLoserHarmonicDiagonal n := by
  classical
  have hz (p : ℕ) (hp : p≠primeLoser n) :
      (p : ℝ)*(primeLoserHarmonicTerm p n)^2=0 := by
    simp [primeLoserHarmonicTerm,Ne.symm hp]
  rw [tsum_eq_single (primeLoser n) hz]
  simp only [primeLoserHarmonicTerm,if_true,div_pow,factorSign_sq,
    primeLoserHarmonicDiagonal,mul_one_div]

/-- Finite total squared-increment mass, with the critical prime weight.
No orthogonality or convergence of the sum of increments is implied. -/
theorem summable_primeLoserHarmonic_weighted_square_rows :
    Summable (fun n : ℕ => ∑' p : ℕ, (p : ℝ)*(primeLoserHarmonicTerm p n)^2) := by
  simpa only [primeLoserHarmonicTerm_weighted_square_row] using
    summable_primeLoserHarmonicDiagonal

lemma primeLoserHarmonicDiagonal_tail_zero :
    Tendsto (fun N : ℕ => ∑' j, primeLoserHarmonicDiagonal (j+N)) atTop (𝓝 0) := by
  have h := summable_primeLoserHarmonicDiagonal.hasSum.tendsto_sum_nat
  have he (N : ℕ) : (∑' j, primeLoserHarmonicDiagonal (j+N)) =
      (∑' n, primeLoserHarmonicDiagonal n)-∑ n ∈ range N, primeLoserHarmonicDiagonal n := by
    have hh := summable_primeLoserHarmonicDiagonal.sum_add_tsum_nat_add N
    linarith
  simp_rw [he]
  simpa only [sub_self] using h.const_sub (∑' n, primeLoserHarmonicDiagonal n)

#print axioms summable_primeLoserHarmonicDiagonal
#print axioms summable_primeLoserHarmonic_weighted_square_rows
#print axioms primeLoserHarmonicDiagonal_tail_zero
end Erdos371
