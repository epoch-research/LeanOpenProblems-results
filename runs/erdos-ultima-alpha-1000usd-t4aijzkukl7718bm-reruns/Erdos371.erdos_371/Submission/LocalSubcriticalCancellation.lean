import FormalConjecturesUtil
import Submission.SubcriticalPrimePairCancellation

/-! Changing the global product cutoff to the local product cutoff causes
exactly zero signed error. The score still counts all prime-divisor pairs. -/

namespace Erdos371LocalSubcriticalCancellation

open Finset Filter Erdos371CofactorSieve Erdos371SubcriticalPrimePairCancellation
open scoped Topology

/-- The part of a pair count that meets the input-dependent product cutoff. -/
def localCount (a b N : ℕ) : ℕ :=
  ((range N).filter fun n => a ∣ n ∧ b ∣ n+1 ∧ a*b ≤ n+1).card

lemma initial_count_one {a b N : ℕ} (ha : 1 < a) (hb : 0 < b)
    (hab : a.Coprime b) (hN : a*b ≤ N) :
    ((range N).filter fun n => a ∣ n ∧ b ∣ n+1 ∧ n+1 < a*b).card = 1 := by
  obtain ⟨v,hv,hav,hbv⟩ := exists_progression_origin (by omega) hb hab
  have hv' : v+1 < a*b := by
    have hvne : v+1 ≠ a*b := by
      intro he
      have hd : a ∣ v+1 := he ▸ dvd_mul_right a b
      have h1 : a ∣ 1 := by simpa using Nat.dvd_sub hd hav
      have := Nat.dvd_one.mp h1
      omega
    omega
  have he : (range N).filter (fun n => a ∣ n ∧ b ∣ n+1 ∧ n+1 < a*b) = {v} := by
    ext n
    simp only [mem_filter, mem_range, mem_singleton]
    constructor
    · rintro ⟨hn,han,hbn,hnab⟩
      have hh := progression_remainder hab hv hav hbv han hbn
      simpa [Nat.mod_eq_of_lt (by omega : n < a*b)] using hh
    · rintro rfl
      exact ⟨by omega,hav,hbv,hv'⟩
  rw [he,card_singleton]

lemma count_eq_localCount_add_one {a b N : ℕ} (ha : 1 < a) (hb : 0 < b)
    (hab : a.Coprime b) (hN : a*b ≤ N) :
    count a b N = localCount a b N + 1 := by
  rw [← initial_count_one ha hb hab hN]
  unfold count localCount
  rw [← card_union_of_disjoint (s := (range N).filter fun n =>
    a ∣ n ∧ b ∣ n+1 ∧ a*b ≤ n+1) (t := (range N).filter fun n =>
    a ∣ n ∧ b ∣ n+1 ∧ n+1 < a*b) (by
      apply disjoint_left.mpr
      intro n hn hm
      have hle := (mem_filter.mp hn).2.2.2
      have hlt := (mem_filter.mp hm).2.2.2
      omega)]
  congr 1
  ext n
  simp only [mem_filter,mem_union]
  by_cases h : a*b ≤ n+1
  · simp [h,not_lt_of_ge h]
  · simp [h,lt_of_not_ge h]

lemma reversed_localCount {p q N : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p < q) (hN : p*q ≤ N) :
    (localCount p q N : ℝ) - localCount q p N =
      (count p q N : ℝ) - count q p N := by
  have hc := (Nat.coprime_primes hp hq).mpr hpq.ne
  rw [count_eq_localCount_add_one hp.one_lt hq.pos hc hN,
    count_eq_localCount_add_one hq.one_lt hp.pos hc.symm (by simpa [Nat.mul_comm] using hN)]
  push_cast
  ring

lemma localCount_eq_sum (a b N : ℕ) :
    (localCount a b N : ℝ) =
      ∑ n ∈ range N, if a*b ≤ n+1 then
        (if a ∣ n ∧ b ∣ n+1 then (1:ℝ) else 0) else 0 := by
  simp only [localCount, card_eq_sum_ones, Nat.cast_sum, sum_filter]
  apply sum_congr rfl
  intro n hn
  split_ifs <;> simp_all

lemma localComparison_eq_restricted {n N : ℕ} (hn : n < N) :
    (localComparison (n+1) n : ℝ) =
      ∑ z ∈ pairs N, if z.1*z.2 ≤ n+1 then
        ((if z.1 ∣ n ∧ z.2 ∣ n+1 then (1:ℝ) else 0) -
         (if z.2 ∣ n ∧ z.1 ∣ n+1 then (1:ℝ) else 0)) else 0 := by
  unfold localComparison
  push_cast
  have hsub : pairs (n+1) ⊆ pairs N := by
    rintro ⟨p,q⟩ hz
    obtain ⟨hp,hq,hpq,hle⟩ := mem_pairs.mp hz
    exact mem_pairs.mpr ⟨hp,hq,hpq,by omega⟩
  calc
    _ = ∑ z ∈ pairs (n+1), if z.1*z.2 ≤ n+1 then
        ((if z.1 ∣ n ∧ z.2 ∣ n+1 then (1:ℝ) else 0) -
         (if z.2 ∣ n ∧ z.1 ∣ n+1 then (1:ℝ) else 0)) else 0 := by
      apply sum_congr rfl
      rintro ⟨p,q⟩ hz
      rw [if_pos (mem_pairs.mp hz).2.2.2]
    _ = _ := by
      apply sum_subset hsub
      rintro ⟨p,q⟩ hz hnz
      have hh : ¬ p*q ≤ n+1 := by
        intro hh
        obtain ⟨hp,hq,hpq,_⟩ := mem_pairs.mp hz
        exact hnz (mem_pairs.mpr ⟨hp,hq,hpq,hh⟩)
      exact if_neg hh

/-- The local and global cutoff signed sums are exactly equal. -/
theorem local_sum_eq_discrepancy (N : ℕ) :
    (∑ n ∈ range N, (localComparison (n+1) n : ℝ)) = discrepancy N := by
  calc
    _ = ∑ n ∈ range N, ∑ z ∈ pairs N, if z.1*z.2 ≤ n+1 then
        ((if z.1 ∣ n ∧ z.2 ∣ n+1 then (1:ℝ) else 0) -
         (if z.2 ∣ n ∧ z.1 ∣ n+1 then (1:ℝ) else 0)) else 0 := by
      apply sum_congr rfl
      intro n hn
      exact localComparison_eq_restricted (mem_range.mp hn)
    _ = ∑ z ∈ pairs N, ((localCount z.1 z.2 N : ℝ) - localCount z.2 z.1 N) := by
      rw [sum_comm]
      apply sum_congr rfl
      intro z hz
      rw [localCount_eq_sum,localCount_eq_sum,← sum_sub_distrib]
      apply sum_congr rfl
      intro n hn
      rw [Nat.mul_comm z.2 z.1]
      split_ifs <;> ring
    _ = discrepancy N := by
      unfold discrepancy
      apply sum_congr rfl
      rintro ⟨p,q⟩ hz
      obtain ⟨hp,hq,hpq,hN⟩ := mem_pairs.mp hz
      exact reversed_localCount hp hq hpq hN

/-- Unconditional mean cancellation for locally subcritical prime pairs. -/
theorem local_mean_tendsto_zero :
    Tendsto (fun N : ℕ => (∑ n ∈ range N, (localComparison (n+1) n : ℝ)) / N)
      atTop (𝓝 0) := by
  simpa only [local_sum_eq_discrepancy] using discrepancy_mean_tendsto_zero

end Erdos371LocalSubcriticalCancellation

#print axioms Erdos371LocalSubcriticalCancellation.local_sum_eq_discrepancy
#print axioms Erdos371LocalSubcriticalCancellation.local_mean_tendsto_zero
