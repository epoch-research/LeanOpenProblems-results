import Submission.PrimeLoserPrimeWeightedCollisions
import Submission.PrimeWinnerLogPowerCofactor

/-!
The actual prime-weighted loser diagonal is o(N^2 / (log N)^a) for every
0 <= a < 2. This uses the uniform two-large-prime sieve. It is a diagonal
estimate only; no bound for the signed off-diagonal sum is asserted.
-/
namespace Erdos371
open Finset Filter FiniteSieve
open scoped Topology
set_option autoImplicit false

lemma primeLoserPrimeWeightedDiagonal_threshold_bound (N : ℕ) (T : ℝ)
    (hT : 0 ≤ T) :
    primeLoserPrimeWeightedDiagonal N ≤ (N : ℝ)*T+
      (N : ℝ)*(((range N).filter fun n => T < (primeLoser n : ℝ)).card : ℝ) := by
  have hsub : primeLoserPrimeWeightedDiagonal N ≤ ∑ n ∈ range N, (primeLoser n : ℝ) :=
    sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (by intros; positivity)
  have hpoint (n : ℕ) (hn : n ∈ range N) :
      (primeLoser n : ℝ) ≤ T+(if T < (primeLoser n : ℝ) then (N : ℝ) else 0) := by
    have hp : primeLoser n ≤ N :=
      (min_le_left (Nat.maxPrimeFac n) _).trans (Nat.maxPrimeFac_le.trans
        (mem_range.mp hn).le)
    split_ifs with h
    · have hp' : (primeLoser n : ℝ) ≤ N := by exact_mod_cast hp
      linarith
    · simpa only [add_zero] using not_lt.mp h
  have hh := sum_le_sum hpoint
  simp only [sum_add_distrib, sum_const, card_range, nsmul_eq_mul,
    ← sum_filter] at hh
  simpa only [sum_const, nsmul_eq_mul, mul_comm] using hsub.trans hh

lemma primeLoserPrimeWeightedDiagonal_power_bound (N : ℕ) (u : ℝ)
    (hN : 0 < N) :
    primeLoserPrimeWeightedDiagonal N/(N : ℝ)^2 ≤
      (N : ℝ)^(-u)+((bothLargePrimeSet N u).card : ℝ)/N := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have he : (range N).filter (fun n => (N : ℝ)^(1-u) < (primeLoser n : ℝ)) =
      bothLargePrimeSet N u := by
    ext n
    simp only [bothLargePrimeSet, mem_filter, primeLoser, Nat.cast_min, lt_min_iff]
  have hb := primeLoserPrimeWeightedDiagonal_threshold_bound N ((N : ℝ)^(1-u))
    (Real.rpow_nonneg hN0.le _)
  rw [he] at hb
  have hp : (N : ℝ)^(1-u) = (N : ℝ)*(N : ℝ)^(-u) := by
    rw [sub_eq_add_neg, Real.rpow_add hN0, Real.rpow_one]
  have hd := div_le_div_of_nonneg_right hb (sq_nonneg (N : ℝ))
  apply hd.trans_eq
  rw [hp]
  field_simp

lemma logPowerCofactor_negative_power (b : ℝ) (N : ℕ) (hN : 1 < N) :
    (N : ℝ)^(-logPowerCofactorExponent b N) = 1/(2*(Real.log N)^b) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hL : 0 < Real.log N := Real.log_pos (by exact_mod_cast hN)
  have hp : (N : ℝ)^(logPowerCofactorExponent b N) = 2*(Real.log N)^b := by
    rw [Real.rpow_def_of_pos hN0]
    unfold logPowerCofactorExponent
    rw [mul_div_cancel₀ _ hL.ne']
    exact Real.exp_log (by positivity)
  rw [Real.rpow_neg hN0.le, hp, one_div]

/-- Any fixed logarithmic power strictly below two is absorbed by the
actual diagonal. The bound does not control accumulated signed currents. -/
theorem primeLoserPrimeWeightedDiagonal_log_rpow_zero (a : ℝ)
    (ha : 0 ≤ a) (ha2 : a < 2) :
    Tendsto (fun N : ℕ => (Real.log N)^a*
      primeLoserPrimeWeightedDiagonal N/(N : ℝ)^2) atTop (𝓝 0) := by
  let b : ℝ := a+1
  have hb : 0 ≤ b := by dsimp [b]; linarith
  have hL : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hhead : Tendsto (fun N : ℕ => 1/(2*Real.log N)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (hL.const_mul_atTop (by norm_num : (0 : ℝ) < 2))
  have hmain := ((affine_log_square_div_rpow_tendsto_zero b (2-a)
    (by linarith)).comp hL).const_mul largePairConstant
  have herr := (log_nat_rpow_div_rpow_tendsto_zero a (1/2) (by norm_num)).const_mul
    ((2 : ℝ)^65)
  have ht := (hhead.add hmain).add herr
  simp only [mul_zero, add_zero] at ht
  apply squeeze_zero' (Eventually.of_forall (fun N => by
    have := Real.log_natCast_nonneg N
    unfold primeLoserPrimeWeightedDiagonal
    positivity)) _ ht
  filter_upwards [logPowerCofactor_cutoff_data b hb, eventually_gt_atTop (1 : ℕ)]
    with N hd hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hL0 : 0 < Real.log N := Real.log_pos (by exact_mod_cast hN)
  have hp := primeLoserPrimeWeightedDiagonal_power_bound N (logPowerCofactorExponent b N)
    (by omega)
  have hs := bothLargePrimeSet_ratio_bound N (logPowerCofactorExponent b N)
    hN hd.2.2.1 hd.2.2.2.1
  have hm := mul_le_mul_of_nonneg_left (hp.trans (add_le_add le_rfl hs))
    (Real.rpow_nonneg hL0.le a)
  rw [logPowerCofactor_negative_power b N hN] at hm
  have hu : logPowerCofactorExponent b N =
      (Real.log 2+b*Real.log (Real.log N))/Real.log N := by
    unfold logPowerCofactorExponent
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
      (Real.rpow_pos_of_pos hL0 b).ne', Real.log_rpow hL0]
  have hbp : (Real.log N)^b = (Real.log N)^a*Real.log N := by
    dsimp only [b]
    rw [Real.rpow_add hL0, Real.rpow_one]
  have hexp : (N : ℝ)^(-1/2 : ℝ) = 1/(N : ℝ)^(1/2 : ℝ) := by
    rw [show (-1/2 : ℝ) = -(1/2) by ring, Real.rpow_neg hN0.le]
    exact (one_div _).symm
  rw [hu, hbp, hexp] at hm
  simp only [Function.comp_apply]
  rw [Real.rpow_sub hL0, Real.rpow_two]
  convert hm using 1
  · ring
  · field_simp
    ring

/-- In particular, one logarithmic loss is harmless on the diagonal. -/
theorem primeLoserPrimeWeightedDiagonal_log_zero :
    Tendsto (fun N : ℕ => Real.log N*
      primeLoserPrimeWeightedDiagonal N/(N : ℝ)^2) atTop (𝓝 0) := by
  simpa only [Real.rpow_one] using
    primeLoserPrimeWeightedDiagonal_log_rpow_zero 1 (by norm_num) (by norm_num)

#print axioms primeLoserPrimeWeightedDiagonal_log_rpow_zero
#print axioms primeLoserPrimeWeightedDiagonal_log_zero
end Erdos371
