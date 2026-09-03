import FormalConjecturesUtil
import Submission.LoserGroupConservation
import Submission.WeightedPrimeEnergy

/-! Prime-weighted conservation between winning and losing groups. The two
weighted energies differ by a linear endpoint term. This transfers a
cancellation criterion but does not prove the required cancellation. -/

namespace Erdos371WeightedLoserEnergy

open Finset Filter Erdos371PrimeDiscrepancy Erdos371LoserGroupConservation
open Erdos371WeightedPrimeEnergy Erdos371ElementaryEnergy
open scoped Topology

noncomputable def weightedLoserEnergy (N : ℕ) : ℝ :=
  ∑ p ∈ (N+1).primesBelow, (p:ℝ)*(loserGroup p N:ℝ)^2

lemma weightedLoserEnergy_nonneg (N : ℕ) : 0 ≤ weightedLoserEnergy N := by
  exact sum_nonneg (fun _ _ => by positivity)

lemma weighted_energy_conservation (N : ℕ) :
    weightedEnergy N - weightedLoserEnergy N =
      if 1 < N then (P N:ℝ)*(2*(group (P N) N:ℝ)-1) else 0 := by
  have he (p : ℕ) (hp : p ∈ (N+1).primesBelow) :
      (p:ℝ)*(group p N:ℝ)^2 - (p:ℝ)*(loserGroup p N:ℝ)^2 =
        if P N = p then (p:ℝ)*(2*(group p N:ℝ)-1) else 0 := by
    have hg := prime_group_conservation (Nat.prime_of_mem_primesBelow hp) N
    by_cases h : P N = p
    · simp only [if_pos h] at hg ⊢
      have hg' : (group p N:ℝ) = (loserGroup p N:ℝ)+1 := by exact_mod_cast hg
      rw [hg']
      ring
    · simp only [if_neg h, add_zero] at hg ⊢
      rw [hg]
      ring
  unfold weightedEnergy weightedLoserEnergy
  rw [← sum_sub_distrib, sum_congr rfl he]
  simp only [sum_ite_eq, endpoint_mem_iff]

/-- The prime factor in the weight is cancelled by the bound `|group p N| ≤ N/p`.
The endpoint prime is at most `N`, so the weighted error is still linear. -/
theorem weighted_energy_difference_bound (N : ℕ) :
    |weightedEnergy N-weightedLoserEnergy N| ≤ 3*(N:ℝ) := by
  rw [weighted_energy_conservation]
  split_ifs with hN
  · have hp := Nat.prime_maxPrimeFac_of_one_lt N hN
    have hp' : (0:ℝ) < P N := Nat.cast_pos.mpr hp.pos
    have hg := (group_abs_le_div hp N).trans (Nat.cast_div_le (α := ℝ))
    have hmul : (P N:ℝ)*|(group (P N) N:ℝ)| ≤ N := by
      have hh := (le_div_iff₀ hp').mp hg
      nlinarith
    have hpN : (P N:ℝ) ≤ N := Nat.cast_le.mpr Nat.maxPrimeFac_le
    calc
      _ = (P N:ℝ)*|2*(group (P N) N:ℝ)-1| := by rw [abs_mul, abs_of_pos hp']
      _ ≤ (P N:ℝ)*(2*|(group (P N) N:ℝ)|+1) := by
        apply mul_le_mul_of_nonneg_left _ hp'.le
        have hh := abs_sub (2*(group (P N) N:ℝ)) 1
        norm_num [abs_mul] at hh
        exact hh
      _ ≤ _ := by nlinarith
  · simp only [abs_zero]
    positivity

lemma weightedLoserEnergy_le_sq_add_linear (N : ℕ) :
    weightedLoserEnergy N ≤ (N:ℝ)^2+3*(N:ℝ) := by
  have hh := (abs_le.mp (weighted_energy_difference_bound N)).1
  have hw := weightedEnergy_le_sq N
  linarith

lemma normalized_difference_tendsto_zero :
    Tendsto (fun N : ℕ =>
      (weightedEnergy N-weightedLoserEnergy N)/(N:ℝ)^2) atTop (𝓝 0) := by
  apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (tendsto_const_div_atTop_nhds_zero_nat 3)
  · exact Eventually.of_forall fun _ => abs_nonneg _
  · filter_upwards [eventually_gt_atTop 0] with N hN
    have hn : (N:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
    change |(weightedEnergy N-weightedLoserEnergy N)/(N:ℝ)^2| ≤ 3/(N:ℝ)
    rw [abs_div, abs_of_nonneg (sq_nonneg (N:ℝ))]
    calc
      _ ≤ 3*(N:ℝ)/(N:ℝ)^2 :=
        div_le_div_of_nonneg_right (weighted_energy_difference_bound N) (sq_nonneg _)
      _ = _ := by field_simp

/-- Either weighted grouping has the same quadratic-scale little-o condition. -/
theorem weighted_energy_littleO_iff :
    Tendsto (fun N : ℕ => weightedEnergy N/(N:ℝ)^2) atTop (𝓝 0) ↔
      Tendsto (fun N : ℕ => weightedLoserEnergy N/(N:ℝ)^2) atTop (𝓝 0) := by
  constructor
  · intro h
    have hh := h.sub normalized_difference_tendsto_zero
    simp only [sub_zero] at hh
    apply hh.congr
    intro N
    ring
  · intro h
    have hh := h.add normalized_difference_tendsto_zero
    simp only [add_zero] at hh
    apply hh.congr
    intro N
    ring

/-- The remaining losing-prime estimate would suffice; it is not proved here. -/
theorem density_half_of_weightedLoserEnergy_subquadratic
    (hW : Tendsto (fun N : ℕ => weightedLoserEnergy N/(N:ℝ)^2) atTop (𝓝 0)) :
    {n | P n < P (n+1)}.HasDensity (1/2) :=
  density_half_of_weightedEnergy_subquadratic (weighted_energy_littleO_iff.mpr hW)

end Erdos371WeightedLoserEnergy

#print axioms Erdos371WeightedLoserEnergy.weighted_energy_difference_bound
#print axioms Erdos371WeightedLoserEnergy.weighted_energy_littleO_iff

#print axioms Erdos371WeightedLoserEnergy.density_half_of_weightedLoserEnergy_subquadratic
