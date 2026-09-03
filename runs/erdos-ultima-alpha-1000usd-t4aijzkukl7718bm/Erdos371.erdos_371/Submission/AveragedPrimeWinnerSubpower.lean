import Submission.AveragedPrimeWinnerEnergy
import Submission.PrimeWinnerSubpowerEnergy

/-! A subpower-loss bound on cumulative, rather than pointwise, prime-winner
energy suffices for Erdős 371. No such arithmetic bound is asserted here. -/
namespace Erdos371
open Finset Filter
open scoped Topology

lemma primeWinnerLowSum_eq_prefix (B N : ℕ) :
    primeWinnerLowSum B N =
      ∑ n ∈ range N, if primeWinner n ≤ B then factorSign n else 0 := by
  unfold primeWinnerLowSum primeWinnerSum
  rw [sum_fiberwise_eq_sum_filter,sum_filter]
  apply sum_congr rfl
  intro n hn
  simp only [mem_filter,primeWinner_mem_labels N n hn,true_and]

/-- Persistence applied after fixing the prime cutoff. The same cutoff is
used at every nearby endpoint, so no moving-cutoff identification is needed. -/
theorem primeWinnerLowSum_cube_le_cumulative (B N : ℕ) :
    |primeWinnerLowSum B N|^3 ≤
      8*(B+1 : ℝ)*cumulativePrimeWinnerEnergy (2*N) := by
  have hf (n : ℕ) : |if primeWinner n ≤ B then factorSign n else 0| ≤ (1 : ℝ) := by
    split_ifs
    · simpa only [← Real.norm_eq_abs,factorSign_norm] using (le_refl (1 : ℝ))
    · norm_num
  have h := unit_prefix_cube_le_square_sum
    (fun n => if primeWinner n ≤ B then factorSign n else 0) hf N
  simp_rw [← primeWinnerLowSum_eq_prefix] at h
  have hs := sum_le_sum (fun k (_ : k ∈ range (2*N+1)) => primeWinnerLowSum_sq_le B k)
  rw [← mul_sum] at hs
  exact h.trans (by
    simpa only [cumulativePrimeWinnerEnergy,mul_assoc] using
      mul_le_mul_of_nonneg_left hs (by norm_num : (0 : ℝ) ≤ 8))

lemma primeWinnerLowSum_power_zero_of_cumulative (u : ℝ) (hu0 : 0<u) (hu : u≤1/8)
    (hE : ∀ᶠ X : ℕ in atTop,
      cumulativePrimeWinnerEnergy X ≤ (X : ℝ)^(2+u/2)) :
    Tendsto (fun N : ℕ => primeWinnerLowSum ⌈(N : ℝ)^(1-u)⌉₊ N/N) atTop (𝓝 0) := by
  have hN : Tendsto (fun N : ℕ => 2*N) atTop atTop :=
    tendsto_atTop_mono (fun N => by dsimp; omega) tendsto_id
  have ht1 : Tendsto (fun N : ℕ => (N : ℝ)^(-u/2)) atTop (𝓝 0) := by
    simpa only [neg_div] using
      (tendsto_rpow_neg_atTop (half_pos hu0)).comp tendsto_natCast_atTop_atTop
  have ht2 : Tendsto (fun N : ℕ => (N : ℝ)^(-1+u/2)) atTop (𝓝 0) := by
    rw [show -1+u/2 = -(1-u/2) by ring]
    exact (tendsto_rpow_neg_atTop (show 0<1-u/2 by linarith)).comp
      tendsto_natCast_atTop_atTop
  have ht := (ht1.add (ht2.const_mul 2)).const_mul (8*(2 : ℝ)^(2+u/2))
  simp only [mul_zero,add_zero] at ht
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [hN.eventually hE,ht.eventually_lt_const (pow_pos hε 3),
    eventually_gt_atTop (0 : ℕ)] with N hEN he hpos
  have hNr : (0 : ℝ)<N := by exact_mod_cast hpos
  have hceil : (⌈(N : ℝ)^(1-u)⌉₊ : ℝ)+1 ≤ (N : ℝ)^(1-u)+2 := by
    have h := Nat.ceil_lt_add_one (Real.rpow_nonneg hNr.le (1-u))
    linarith
  have hs : |primeWinnerLowSum ⌈(N : ℝ)^(1-u)⌉₊ N|^3 ≤
      8*((N : ℝ)^(1-u)+2)*((2*N : ℕ) : ℝ)^(2+u/2) := by
    apply (primeWinnerLowSum_cube_le_cumulative ⌈(N : ℝ)^(1-u)⌉₊ N).trans
    exact mul_le_mul (mul_le_mul_of_nonneg_left hceil (by norm_num)) hEN
      (cumulativePrimeWinnerEnergy_nonneg (2*N)) (by positivity)
  have hpow1 : (N : ℝ)^(1-u)*(N : ℝ)^(2+u/2)/(N : ℝ)^3 = (N : ℝ)^(-u/2) := by
    rw [← Real.rpow_add hNr,← Real.rpow_natCast,← Real.rpow_sub hNr]
    congr 1
    ring
  have hpow2 : (N : ℝ)^(2+u/2)/(N : ℝ)^3 = (N : ℝ)^(-1+u/2) := by
    rw [← Real.rpow_natCast,← Real.rpow_sub hNr]
    congr 1
    ring
  have hid : (8*((N : ℝ)^(1-u)+2)*((2*N : ℕ) : ℝ)^(2+u/2))/(N : ℝ)^3 =
      (8*(2 : ℝ)^(2+u/2))*((N : ℝ)^(-u/2)+2*(N : ℝ)^(-1+u/2)) := by
    rw [Nat.cast_mul,Nat.cast_ofNat,Real.mul_rpow (by norm_num : (0 : ℝ)≤2) hNr.le]
    calc
      _ = (8*(2 : ℝ)^(2+u/2))*
          ((N : ℝ)^(1-u)*(N : ℝ)^(2+u/2)/(N : ℝ)^3+
            2*((N : ℝ)^(2+u/2)/(N : ℝ)^3)) := by ring
      _ = _ := by rw [hpow1,hpow2]
  have hb := div_le_div_of_nonneg_right hs (pow_nonneg hNr.le 3)
  rw [hid] at hb
  have hc : |primeWinnerLowSum ⌈(N : ℝ)^(1-u)⌉₊ N/N|^3 < ε^3 := by
    rw [abs_div,abs_of_pos hNr,div_pow]
    exact hb.trans_lt he
  simp only [dist_zero_right,Real.norm_eq_abs]
  by_contra h
  exact (not_lt_of_ge (pow_le_pow_left₀ hε.le (le_of_not_gt h) 3)) hc

open FiniteSieve in
/-- The arithmetic energy estimate is only required after averaging over
endpoints. It remains a hypothesis, not a proved cancellation theorem. -/
theorem density_of_subpower_cumulative_primeWinnerEnergy
    (hE : ∀ η : ℝ, 0<η → ∀ᶠ X : ℕ in atTop,
      cumulativePrimeWinnerEnergy X ≤ (X : ℝ)^(2+η)) :
    {n | Nat.maxPrimeFac (n+1)>Nat.maxPrimeFac n}.HasDensity (1/2) := by
  rw [density_iff_signed_count]
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hC : 0 ≤ largePairConstant := by unfold largePairConstant; positivity
  have hden : 0 < 4*(largePairConstant+1) := by positivity
  let u : ℝ := min (1/8) (ε/(4*(largePairConstant+1)))
  have hu0 : 0<u := lt_min (by norm_num) (div_pos hε hden)
  have hu : u≤1/8 := min_le_left _ _
  have huε : u*(4*(largePairConstant+1)) ≤ ε :=
    (le_div_iff₀ hden).mp (min_le_right _ _)
  have husq : u^2 ≤ u := by nlinarith [hu0.le]
  have hcu : largePairConstant*u^2 ≤ ε/4 := by
    have hh := mul_le_mul_of_nonneg_left husq hC
    nlinarith [hu0.le]
  have hlow := primeWinnerLowSum_power_zero_of_cumulative u hu0 hu (hE (u/2) (half_pos hu0))
  have hhigh := primeWinnerL1Above_top_eventually_le (fun N => ⌈(N : ℝ)^(1-u)⌉₊)
    u hu0.le hu (Eventually.of_forall fun N => Nat.le_ceil _) (ε/4) (by positivity)
  have hl := (Metric.tendsto_nhds.mp hlow) (ε/4) (by positivity)
  filter_upwards [hl,hhigh] with N hlN hhN
  simp only [dist_zero_right] at hlN ⊢
  have hb := div_le_div_of_nonneg_right
    (signedCount_norm_le_low_add_high ⌈(N : ℝ)^(1-u)⌉₊ N) (Nat.cast_nonneg (α := ℝ) N)
  rw [add_div] at hb
  have hn (x : ℝ) : ‖x‖/(N : ℝ) = ‖x/N‖ := by
    rw [norm_div,Real.norm_natCast]
  rw [hn,hn] at hb
  linarith

#print axioms primeWinnerLowSum_cube_le_cumulative
#print axioms density_of_subpower_cumulative_primeWinnerEnergy
end Erdos371
