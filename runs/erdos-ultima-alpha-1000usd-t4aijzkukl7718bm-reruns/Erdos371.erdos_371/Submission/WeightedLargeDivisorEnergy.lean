import FormalConjecturesUtil
import Submission.LargeDivisorSignedEnergy

/-! A linear bound for logarithmically weighted large-divisor signed energy.
This is not a bound for the unrestricted winning-prime energy. -/

namespace Erdos371WeightedLargeDivisorEnergy

open Finset Erdos371PrimeDiscrepancy Erdos371ProductSignTransport
open Erdos371LargeDivisorSignedEnergy Erdos371RadicalLogMean

noncomputable def weight (N q : ℕ) : ℝ := Real.log (q : ℝ) / Real.log (N : ℝ)

lemma weight_nonneg (N q : ℕ) : 0 ≤ weight N q :=
  div_nonneg (Real.log_natCast_nonneg _) (Real.log_natCast_nonneg _)

lemma divisor_weight_sum {N n : ℕ} (hn : 0 < n) (hnN : n ≤ N) :
    (∑ q ∈ (N+1).primesBelow, if q ∣ n then weight N q else 0) = level N n := by
  rw [← Erdos371AffinePrimeOccurrenceExcess.primeWeight_expand (weight N) hn hnN]
  simp only [Erdos371AffinePrimeOccurrenceExcess.primeWeight, weight, level, radLog, sum_div]

lemma member_weight_expand (N p q : ℕ) :
    weight N q * (members p q N).card =
      ∑ n ∈ range N, if winner n=p ∧ q ∣ lower n then weight N q else 0 := by
  rw [← sum_filter]
  simp [members, mul_comm]

lemma input_weight_sum {N n : ℕ} (hn : n < N) :
    (∑ p ∈ (N+1).primesBelow, ∑ q ∈ (N+1).primesBelow,
      if winner n=p ∧ q ∣ lower n then weight N q else 0) =
        if n=0 then 0 else level N (lower n) := by
  by_cases hn0 : n=0
  · subst n
    have hw : winner 0=1 := by decide +kernel
    rw [if_pos rfl]
    apply sum_eq_zero
    intro p hp
    have hp1 : 1 ≠ p := (Nat.prime_of_mem_primesBelow hp).ne_one.symm
    simp [hw,hp1]
  · have hw : winner n ∈ (N+1).primesBelow := Nat.mem_primesBelow.mpr
      ⟨Nat.lt_succ_of_le (winner_le hn),winner_prime (by omega)⟩
    have hlo := lower_bounds n
    have he : ∀ p, (∑ q ∈ (N+1).primesBelow,
        if winner n=p ∧ q ∣ lower n then weight N q else 0) =
          if winner n=p then level N (lower n) else 0 := by
      intro p
      by_cases hp : winner n=p
      · simp only [hp,true_and,if_true]
        exact divisor_weight_sum (by omega) (by omega)
      · simp [hp]
    simp_rw [he]
    simp [hw,hn0]

lemma weighted_member_count_eq (N : ℕ) :
    (∑ p ∈ (N+1).primesBelow, ∑ q ∈ (N+1).primesBelow,
      weight N q * (members p q N).card) =
      ∑ n ∈ range N, if n=0 then 0 else level N (lower n) := by
  simp_rw [member_weight_expand]
  conv_lhs => arg 2; ext p; rw [sum_comm]
  rw [sum_comm]
  exact sum_congr rfl (fun n hn => input_weight_sum (mem_range.mp hn))

lemma weighted_member_count_le {N : ℕ} (hN : 1 < N) :
    (∑ p ∈ (N+1).primesBelow, ∑ q ∈ (N+1).primesBelow,
      weight N q * (members p q N).card) ≤ N := by
  rw [weighted_member_count_eq]
  calc
    _ ≤ ∑ _n ∈ range N, (1 : ℝ) := by
      apply sum_le_sum
      intro n hn
      by_cases hn0 : n=0
      · simp [hn0]
      · rw [if_neg hn0]
        exact (level_bounds hN (by have := mem_range.mp hn; have := lower_bounds n; omega)).2
    _ = _ := by simp

noncomputable def energy (N : ℕ) : ℝ :=
  ∑ p ∈ (N+1).primesBelow, ∑ q ∈ (N+1).primesBelow,
    if N < p*q then weight N q * (restrictedGroup p q N)^2 else 0

lemma energy_nonneg (N : ℕ) : 0 ≤ energy N := by
  apply sum_nonneg
  intro p hp
  apply sum_nonneg
  intro q hq
  split_ifs
  · exact mul_nonneg (weight_nonneg N q) (sq_nonneg _)
  · exact le_rfl

/-- The large-divisor restricted energy has a linear upper bound. -/
theorem energy_le {N : ℕ} (hN : 1 < N) : energy N ≤ N := by
  apply le_trans _ (weighted_member_count_le hN)
  apply sum_le_sum
  intro p hp
  apply sum_le_sum
  intro q hq
  split_ifs with hprod
  · exact mul_le_mul_of_nonneg_left (restrictedGroup_square_le_card hprod) (weight_nonneg N q)
  · exact mul_nonneg (weight_nonneg N q) (Nat.cast_nonneg _)

end Erdos371WeightedLargeDivisorEnergy

#print axioms Erdos371WeightedLargeDivisorEnergy.energy_le
