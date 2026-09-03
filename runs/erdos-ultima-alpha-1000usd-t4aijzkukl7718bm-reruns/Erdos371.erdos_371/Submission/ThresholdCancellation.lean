import FormalConjecturesUtil
import Submission.PrimeDiscrepancy

/-! Exact cancellation across a largest-prime-factor threshold. This file does
not assert cancellation for comparisons whose endpoints are on the same side. -/

namespace Erdos371ThresholdCancellation

open Erdos371PrimeDiscrepancy

def highIndicator (K n : ℕ) : ℤ := if K < P n then 1 else 0

def highInternal (K N : ℕ) : ℤ :=
  ∑ n ∈ Finset.range N, if K < P n ∧ K < P (n+1) then sign n else 0

def lowInternal (K N : ℕ) : ℤ :=
  ∑ n ∈ Finset.range N, if winner n ≤ K then sign n else 0

def highPairCount (K N : ℕ) : ℕ :=
  ((Finset.range N).filter fun n => K < P n ∧ K < P (n+1)).card

lemma threshold_identity (K n : ℕ) :
    (if K < winner n then sign n else 0) =
      highIndicator K (n+1) - highIndicator K n +
        if K < P n ∧ K < P (n+1) then sign n else 0 := by
  unfold highIndicator winner sign
  simp only [max_def]
  split_ifs <;> omega

lemma sum_high_comparisons (K N : ℕ) :
    (∑ n ∈ Finset.range N, if K < winner n then sign n else 0) =
      highIndicator K N + highInternal K N := by
  simp_rw [threshold_identity]
  rw [Finset.sum_add_distrib, Finset.sum_range_sub]
  simp [highIndicator, P, highInternal]

lemma high_winner_mem_iff {K N n : ℕ} (hK : 1 ≤ K) (hn : n < N) :
    winner n ∈ ((N+1).primesBelow.filter fun p => K < p) ↔ K < winner n := by
  constructor
  · intro h
    exact (Finset.mem_filter.mp h).2
  · intro h
    have hn0 : 0 < n := by
      by_contra hz
      have he : n = 0 := by omega
      subst n
      have hw : winner 0 = 1 := by decide +kernel
      omega
    exact Finset.mem_filter.mpr
      ⟨Nat.mem_primesBelow.mpr ⟨Nat.lt_succ_of_le (winner_le hn), winner_prime hn0⟩, h⟩

/-- Comparisons crossing a cutoff cancel, except at the endpoint. The only
remaining signed sum has both largest prime factors above the cutoff. -/
theorem high_prime_groups (K N : ℕ) (hK : 1 ≤ K) :
    (∑ p ∈ ((N+1).primesBelow.filter fun p => K < p), group p N) =
      highIndicator K N + highInternal K N := by
  rw [← sum_high_comparisons]
  unfold group
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  simp only [Finset.sum_ite_eq]
  simp only [high_winner_mem_iff hK (Finset.mem_range.mp hn)]

/-- The two same-side signed sums account for the full discrepancy, up to one
endpoint indicator. No assertion about either same-side sum is made here. -/
theorem total_split (K N : ℕ) :
    total N = lowInternal K N + highInternal K N + highIndicator K N := by
  have he := Finset.sum_filter_add_sum_filter_not (Finset.range N)
    (fun n => winner n ≤ K) sign
  simp only [Finset.sum_filter, not_le] at he
  rw [sum_high_comparisons] at he
  change lowInternal K N + (highIndicator K N + highInternal K N) = total N at he
  omega

lemma highInternal_abs_le (K N : ℕ) :
    |highInternal K N| ≤ highPairCount K N := by
  unfold highInternal highPairCount
  calc
    _ ≤ ∑ n ∈ Finset.range N,
        |if K < P n ∧ K < P (n+1) then sign n else 0| := Finset.abs_sum_le_sum_abs _ _
    _ = _ := by
      have hs (n : ℕ) : |sign n| = 1 := by unfold sign; split_ifs <;> norm_num
      simp [abs_ite, hs]

/-- An unconditional tail bound using simultaneous, rather than one-sided,
large-prime events. -/
theorem high_prime_groups_abs_le (K N : ℕ) (hK : 1 ≤ K) :
    |∑ p ∈ ((N+1).primesBelow.filter fun p => K < p), group p N| ≤
      highPairCount K N + 1 := by
  rw [high_prime_groups K N hK]
  have hi : |highIndicator K N| ≤ 1 := by
    unfold highIndicator
    split_ifs <;> norm_num
  have hh := highInternal_abs_le K N
  exact (abs_add_le _ _).trans (by omega)

end Erdos371ThresholdCancellation

#print axioms Erdos371ThresholdCancellation.high_prime_groups
#print axioms Erdos371ThresholdCancellation.total_split
#print axioms Erdos371ThresholdCancellation.high_prime_groups_abs_le
