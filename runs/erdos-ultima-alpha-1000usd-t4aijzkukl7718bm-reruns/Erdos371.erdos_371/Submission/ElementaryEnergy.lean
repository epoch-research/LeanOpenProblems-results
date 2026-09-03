import FormalConjecturesUtil
import Submission.PrimeEnergy
import Submission.SmoothDensity

/-! An unconditional subquadratic bound for the winning-prime energy.
This is weaker than the `o(N log N)` bound needed by the established criterion. -/

namespace Erdos371ElementaryEnergy

open Erdos371PrimeDiscrepancy Erdos371PrimeEnergy Erdos371Exploration Filter
open scoped Topology

lemma sign_abs (n : ℕ) : |(sign n : ℝ)| = 1 := by
  unfold sign
  split_ifs <;> norm_num

lemma group_abs_le_count (p N : ℕ) :
    |(group p N : ℝ)| ≤
      (((Finset.range N).filter (fun n => winner n = p)).card : ℝ) := by
  have he : (group p N : ℝ) =
      ∑ n ∈ Finset.range N, if winner n = p then (sign n : ℝ) else 0 := by
    simp [group]
  rw [he]
  calc
    _ ≤ ∑ n ∈ Finset.range N,
        |if winner n = p then (sign n : ℝ) else 0| := Finset.abs_sum_le_sum_abs _ _
    _ = _ := by simp [abs_ite, sign_abs]

lemma sum_group_abs_le (s : Finset ℕ) (N : ℕ) :
    (∑ p ∈ s, |(group p N : ℝ)|) ≤ N := by
  calc
    _ ≤ ∑ p ∈ s, (((Finset.range N).filter (fun n => winner n = p)).card : ℝ) :=
      Finset.sum_le_sum (fun p _ => group_abs_le_count p N)
    _ = ∑ n ∈ Finset.range N, (if winner n ∈ s then (1 : ℝ) else 0) := by
      simp only [← Finset.sum_boole]
      rw [Finset.sum_comm]
      simp
    _ ≤ ∑ _n ∈ Finset.range N, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      split_ifs <;> norm_num
    _ = N := by simp

lemma group_abs_le_div {p : ℕ} (hp : p.Prime) (N : ℕ) :
    |(group p N : ℝ)| ≤ (N / p : ℕ) := by
  have hu : ((Finset.range N).filter (fun n => P (n + 1) = p ∧ P n < p)).card ≤ N / p := by
    rw [← Nat.card_multiples N p]
    apply Finset.card_le_card
    intro n hn
    obtain ⟨hnN, hnP, _⟩ := Finset.mem_filter.mp hn
    exact Finset.mem_filter.mpr ⟨hnN, hnP ▸ Nat.maxPrimeFac_dvd⟩
  have hd : ((Finset.range N).filter (fun n => P n = p ∧ P (n + 1) < p)).card ≤ N / p := by
    rw [← Nat.card_multiples' N p]
    apply Finset.card_le_card
    intro n hn
    obtain ⟨hnN, hnP, _⟩ := Finset.mem_filter.mp hn
    have hn0 : n ≠ 0 := by
      intro he
      subst n
      simp only [P, Nat.maxPrimeFac_zero] at hnP
      exact hp.ne_zero hnP.symm
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by
      have := Finset.mem_range.mp hnN
      omega), hn0, hnP ▸ Nat.maxPrimeFac_dvd⟩
  rw [group_eq_counts]
  push_cast
  apply abs_sub_le_iff.mpr
  constructor <;> linarith [Nat.cast_le (α := ℝ).mpr hu, Nat.cast_le (α := ℝ).mpr hd,
    (Nat.cast_nonneg (((Finset.range N).filter (fun n => P (n + 1) = p ∧ P n < p)).card) :
      (0 : ℝ) ≤ _),
    (Nat.cast_nonneg (((Finset.range N).filter (fun n => P n = p ∧ P (n + 1) < p)).card) :
      (0 : ℝ) ≤ _)]

lemma group_abs_le_small_count {p K : ℕ} (hpK : p ≤ K) (N : ℕ) :
    |(group p N : ℝ)| ≤
      (((Finset.range N).filter (fun n => P n ≤ K)).card : ℝ) := by
  apply (group_abs_le_count p N).trans
  apply Nat.cast_le.mpr
  apply Finset.card_le_card
  intro n hn
  obtain ⟨hnN, hnp⟩ := Finset.mem_filter.mp hn
  refine Finset.mem_filter.mpr ⟨hnN, ?_⟩
  calc
    P n ≤ winner n := le_max_left _ _
    _ = p := hnp
    _ ≤ K := hpK

lemma energy_cutoff_bound {K : ℕ} (hK : 0 < K) (N : ℕ) :
    energy N ≤
      ((((Finset.range N).filter (fun n => P n ≤ K)).card : ℝ) + (N : ℝ) / K) * N := by
  let B : ℝ := (((Finset.range N).filter (fun n => P n ≤ K)).card : ℝ) + (N : ℝ) / K
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hbound {p : ℕ} (hp : p.Prime) : |(group p N : ℝ)| ≤ B := by
    by_cases hpK : p ≤ K
    · apply (group_abs_le_small_count hpK N).trans
      exact le_add_of_nonneg_right (by positivity)
    · have hKp : K ≤ p := by omega
      calc
        _ ≤ ((N / p : ℕ) : ℝ) := group_abs_le_div hp N
        _ ≤ (N : ℝ) / p := Nat.cast_div_le
        _ ≤ (N : ℝ) / K := div_le_div_of_nonneg_left (Nat.cast_nonneg N)
          (Nat.cast_pos.mpr hK) (Nat.cast_le.mpr hKp)
        _ ≤ B := le_add_of_nonneg_left (Nat.cast_nonneg _)
  change energy N ≤ B * N
  calc
    _ ≤ ∑ p ∈ (N + 1).primesBelow, B * |(group p N : ℝ)| := by
      apply Finset.sum_le_sum
      intro p hp
      have hb := hbound (Nat.prime_of_mem_primesBelow hp)
      have hm := mul_le_mul_of_nonneg_right hb (abs_nonneg (group p N : ℝ))
      nlinarith [sq_abs (group p N : ℝ)]
    _ = B * ∑ p ∈ (N + 1).primesBelow, |(group p N : ℝ)| :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ B * N := mul_le_mul_of_nonneg_left (sum_group_abs_le _ N) hB

lemma energy_ratio_cutoff_bound {K N : ℕ} (hK : 0 < K) (hN : 0 < N) :
    energy N / (N : ℝ)^2 ≤
      {n | P n ≤ K}.partialDensity Set.univ N + 1 / (K : ℝ) := by
  rw [bounded_maxPrimeFac_partialDensity]
  calc
    _ ≤ (((((Finset.range N).filter (fun n => P n ≤ K)).card : ℝ) + (N : ℝ) / K) * N) /
        (N : ℝ)^2 := div_le_div_of_nonneg_right (energy_cutoff_bound hK N) (sq_nonneg _)
    _ = _ := by
      have hn : (N : ℝ) ≠ 0 := (Nat.cast_pos.mpr hN).ne'
      have hk : (K : ℝ) ≠ 0 := (Nat.cast_pos.mpr hK).ne'
      field_simp

lemma energy_div_sq_tendsto_zero :
    Tendsto (fun N : ℕ => energy N / (N : ℝ)^2) atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨K, hK, hrecip⟩ := ((eventually_gt_atTop 0).and
    (tendsto_one_div_atTop_nhds_zero_nat.eventually (gt_mem_nhds (half_pos hε)))).exists
  have hs := (bounded_maxPrimeFac_hasDensity_zero K).eventually (gt_mem_nhds (half_pos hε))
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hs
  refine ⟨max N₀ 1, fun N hN => ?_⟩
  have hNpos : 0 < N := by omega
  have hb := energy_ratio_cutoff_bound hK hNpos
  have hsmall := hN₀ N (by omega)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (div_nonneg (energy_nonneg N) (sq_nonneg _))]
  change 1 / (K : ℝ) < ε / 2 at hrecip
  linarith

end Erdos371ElementaryEnergy

#print axioms Erdos371ElementaryEnergy.energy_cutoff_bound
#print axioms Erdos371ElementaryEnergy.energy_div_sq_tendsto_zero
