import Submission.PrimeWinnerPrimeWeightedEnergy
import Submission.PrimeWinnerSubpowerEnergy

/-! The earlier subpower-loss energy hypothesis implies the newer
prime-weighted criterion. Neither hypothesis is proved here. -/
namespace Erdos371
open Finset Filter FiniteSieve
open scoped Topology

lemma primeWeightedEnergy_le_low_energy_add_high_l1 (B N : ℕ) (hN : 0<N) :
    primeWinnerPrimeWeightedEnergy N ≤
      (B : ℝ)*primeWinnerEnergy N+3*N*primeWinnerL1Above B N := by
  let L := (primeWinnerLabels N).filter (·≤B)
  let H := (primeWinnerLabels N).filter (B < ·)
  have he : primeWinnerPrimeWeightedEnergy N =
      (∑ p ∈ L, (p : ℝ)*(primeWinnerSum p N)^2)+
        ∑ p ∈ H, (p : ℝ)*(primeWinnerSum p N)^2 := by
    simpa only [not_le] using (sum_filter_add_sum_filter_not (primeWinnerLabels N)
      (fun p => p≤B) (fun p => (p : ℝ)*(primeWinnerSum p N)^2)).symm
  have hl : (∑ p ∈ L, (p : ℝ)*(primeWinnerSum p N)^2) ≤ (B : ℝ)*primeWinnerEnergy N := by
    calc
      _ ≤ ∑ p ∈ L, (B : ℝ)*(primeWinnerSum p N)^2 := sum_le_sum fun p hp =>
        mul_le_mul_of_nonneg_right (by exact_mod_cast (mem_filter.mp hp).2) (sq_nonneg _)
      _ = (B : ℝ)*(∑ p ∈ L, (primeWinnerSum p N)^2) := (mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (by intros; positivity)) (Nat.cast_nonneg B)
  have hh : (∑ p ∈ H, (p : ℝ)*(primeWinnerSum p N)^2) ≤ 3*N*primeWinnerL1Above B N := by
    rw [primeWinnerL1Above,mul_sum]
    apply sum_le_sum
    intro p hp
    have hpN : (p : ℝ)≤N := by exact_mod_cast primeWinnerLabel_le N p hN (mem_filter.mp hp).1
    have hn := primeWinnerSum_norm_le_multiples p N
    have hd : (p : ℝ)*((N/p : ℕ) : ℝ)≤N := by exact_mod_cast Nat.mul_div_le N p
    have hpn : (p : ℝ)*‖primeWinnerSum p N‖≤3*N := by
      have h := mul_le_mul_of_nonneg_left hn (Nat.cast_nonneg (α := ℝ) p)
      nlinarith
    have h := mul_le_mul_of_nonneg_right hpn (norm_nonneg (primeWinnerSum p N))
    simpa only [mul_assoc,← pow_two,Real.norm_eq_abs,sq_abs] using h
  rw [he]
  exact add_le_add hl hh

lemma primeWeightedEnergy_power_split (u : ℝ) (hu0 : 0<u) (hu : u≤1/8)
    (N : ℕ) (hN : 0<N) (hE : primeWinnerEnergy N≤(N : ℝ)^(1+u/2)) :
    primeWinnerPrimeWeightedEnergy N/(N : ℝ)^2 ≤
      2*(N : ℝ)^(-u/2)+3*(primeWinnerL1Above (ceilPowerCutoff (1-u) N) N/N) := by
  have hN1 : (1 : ℝ)≤N := by exact_mod_cast hN
  have hN0 : (0 : ℝ)<N := by linarith
  have hpow1 : (1 : ℝ)≤(N : ℝ)^(1-u) := Real.one_le_rpow hN1 (by linarith)
  have hceil := Nat.ceil_lt_add_one (Real.rpow_nonneg hN0.le (1-u))
  change (ceilPowerCutoff (1-u) N : ℝ)<_ at hceil
  have hB : (ceilPowerCutoff (1-u) N : ℝ) ≤ 2*(N : ℝ)^(1-u) := by linarith
  have hprod := mul_le_mul hB hE (by unfold primeWinnerEnergy; positivity) (by positivity)
  have hraw := (primeWeightedEnergy_le_low_energy_add_high_l1 (ceilPowerCutoff (1-u) N) N hN).trans
    (add_le_add hprod le_rfl)
  have hid : (2*(N : ℝ)^(1-u)*(N : ℝ)^(1+u/2)+
      3*N*primeWinnerL1Above (ceilPowerCutoff (1-u) N) N)/(N : ℝ)^2 =
      2*(N : ℝ)^(-u/2)+3*(primeWinnerL1Above (ceilPowerCutoff (1-u) N) N/N) := by
    rw [add_div,mul_assoc,mul_div_assoc,← Real.rpow_add hN0,← Real.rpow_two,
      ← Real.rpow_sub hN0]
    have he : 1-u+(1+u/2)-2 = -u/2 := by ring
    rw [he,Real.rpow_two]
    congr 1
    field_simp
  rw [← hid]
  exact div_le_div_of_nonneg_right hraw (sq_nonneg (N : ℝ))

/-- Every subpower-loss full-energy bound implies the prime-weighted o(N^2)
criterion. The latter is sufficient without requiring such a rate for the
unweighted energy. -/
theorem primeWeightedEnergy_tendsto_of_subpower_energy
    (hE : ∀ η : ℝ, 0<η → ∀ᶠ N : ℕ in atTop,
      primeWinnerEnergy N≤(N : ℝ)^(1+η)) :
    Tendsto (fun N : ℕ => primeWinnerPrimeWeightedEnergy N/(N : ℝ)^2) atTop (nhds 0) := by
  apply tendsto_order.mpr
  constructor
  · intro ε hε
    exact Eventually.of_forall fun N => hε.trans_le (div_nonneg
      (primeWinnerPrimeWeightedEnergy_nonneg N) (sq_nonneg _))
  · intro ε hε
    have hC : 0≤largePairConstant := by unfold largePairConstant; positivity
    let u : ℝ := min (1/8) (ε/(12*(largePairConstant+1)))
    have hu0 : 0<u := lt_min (by norm_num) (by positivity)
    have hu : u≤1/8 := min_le_left _ _
    have hh : u*(12*(largePairConstant+1))≤ε :=
      (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
    have hs : u^2≤u := by nlinarith
    have hc : 3*largePairConstant*u^2≤ε/4 := by
      have h := mul_le_mul_of_nonneg_left hs hC
      nlinarith
    have hpow : Tendsto (fun N : ℕ => 2*(N : ℝ)^(-u/2)) atTop (nhds 0) := by
      have h := ((tendsto_rpow_neg_atTop (half_pos hu0)).comp tendsto_natCast_atTop_atTop).const_mul 2
      simpa only [neg_div,mul_zero] using h
    have hhigh := primeWinnerL1Above_top_eventually_le (fun N => ceilPowerCutoff (1-u) N)
      u hu0.le hu (Eventually.of_forall fun N => Nat.le_ceil _) (ε/12) (by positivity)
    filter_upwards [hE (u/2) (half_pos hu0),hhigh,hpow.eventually_lt_const
      (by positivity : (0 : ℝ)<ε/4),eventually_gt_atTop (0 : ℕ)] with N hEN hhN hpN hN
    exact (primeWeightedEnergy_power_split u hu0 hu N hN hEN).trans_lt (by linarith)

#print axioms primeWeightedEnergy_tendsto_of_subpower_energy
end Erdos371
