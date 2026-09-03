import FormalConjecturesUtil
import Submission.PrimeDiscrepancy

/-! Exact cofactor reindexing of the prime discrepancy. No asymptotic estimate is asserted. -/

namespace Erdos371CofactorDiscrepancy

open Erdos371PrimeDiscrepancy

lemma count_prime_cofactors {p : ℕ} (hp : p.Prime) (N : ℕ)
    (h : ℕ → Prop) [DecidablePred h] :
    ((Finset.range (N + 1)).filter (fun n => P n = p ∧ h n)).card =
      ((Finset.Icc 1 (N / p)).filter (fun k => P k ≤ p ∧ h (k * p))).card := by
  symm
  apply Finset.card_bij (fun k _ => k * p)
  · intro k hk
    obtain ⟨hkI, hPk, hh⟩ := Finset.mem_filter.mp hk
    obtain ⟨hk1, hkN⟩ := Finset.mem_Icc.mp hkI
    have hkbound : k * p ≤ N := (Nat.le_div_iff_mul_le hp.pos).mp hkN
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),
      (prime_multiple_iff hp (by omega)).mpr hPk, hh⟩
  · intro k hk l hl he
    exact Nat.eq_of_mul_eq_mul_right hp.pos he
  · intro n hn
    obtain ⟨hnN, hPn, hh⟩ := Finset.mem_filter.mp hn
    have hn0 : n ≠ 0 := by
      intro he
      subst n
      simp only [P, Nat.maxPrimeFac_zero] at hPn
      exact hp.ne_zero hPn.symm
    have hpn : p ∣ n := hPn ▸ Nat.maxPrimeFac_dvd
    have he : n / p * p = n := Nat.div_mul_cancel hpn
    have hkpos : 0 < n / p := by
      apply Nat.div_pos
      · exact Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hpn
      · exact hp.pos
    have hkbound : n / p ≤ N / p := Nat.div_le_div_right (by
      have := Finset.mem_range.mp hnN
      omega)
    refine ⟨n / p, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hkpos, hkbound⟩,
      ?_, ?_⟩, he⟩
    · apply (prime_multiple_iff hp hkpos).mp
      rwa [he]
    · rwa [he]

lemma count_before_prime {p : ℕ} (hp : p.Prime) (N : ℕ) :
    ((Finset.range N).filter (fun n => P (n + 1) = p ∧ P n < p)).card =
      ((Finset.Icc 1 (N / p)).filter
        (fun k => P k ≤ p ∧ P (k * p - 1) < p)).card := by
  rw [← count_prime_cofactors hp N (fun n => P (n - 1) < p)]
  apply Finset.card_bij (fun n _ => n + 1)
  · intro n hn
    obtain ⟨hnN, hnP, hnlt⟩ := Finset.mem_filter.mp hn
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by
      have := Finset.mem_range.mp hnN
      omega), hnP, by simpa using hnlt⟩
  · intro n hn m hm he
    omega
  · intro m hm
    obtain ⟨hmN, hmP, hmlt⟩ := Finset.mem_filter.mp hm
    have hm0 : m ≠ 0 := by
      intro he
      subst m
      simp only [P, Nat.maxPrimeFac_zero] at hmP
      exact hp.ne_zero hmP.symm
    refine ⟨m - 1, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by
      have := Finset.mem_range.mp hmN
      omega), ?_, hmlt⟩, by omega⟩
    simpa [Nat.sub_add_cancel (by omega : 1 ≤ m)] using hmP

def cofactorDifference (p N : ℕ) : ℤ :=
  (((Finset.Icc 1 (N / p)).filter
    (fun k => P k ≤ p ∧ P (k * p - 1) < p)).card : ℤ) -
  (((Finset.Icc 1 (N / p)).filter
    (fun k => P k ≤ p ∧ P (k * p + 1) < p)).card : ℤ)

lemma group_eq_cofactorDifference {p : ℕ} (hp : p.Prime) (N : ℕ) :
    group p N = cofactorDifference p N +
      (if P N = p ∧ P (N + 1) < p then 1 else 0) := by
  rw [group_eq_counts, count_before_prime hp]
  unfold cofactorDifference
  rw [← count_prime_cofactors hp N (fun n => P (n + 1) < p)]
  rw [Finset.range_add_one, Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (by simp)]
    push_cast
    ring
  · ring

lemma endpoint_sum (N : ℕ) :
    (∑ p ∈ (N + 1).primesBelow,
      (if P N = p ∧ P (N + 1) < p then (1 : ℤ) else 0)) =
      if P (N + 1) < P N then 1 else 0 := by
  simp only [ite_and, Finset.sum_ite_eq]
  by_cases h : P (N + 1) < P N
  · have hN : 1 < N := by
      by_contra hn
      have hsmall : N = 0 ∨ N = 1 := by omega
      rcases hsmall with rfl | rfl <;> norm_num [P] at h
    have hp : P N ∈ (N + 1).primesBelow := Nat.mem_primesBelow.mpr
      ⟨Nat.lt_succ_of_le Nat.maxPrimeFac_le,
        Nat.prime_maxPrimeFac_of_one_lt N hN⟩
    simp [hp, h]
  · simp [h]

lemma total_eq_cofactor_sum {N : ℕ} (hN : 0 < N) :
    total N = 1 + (∑ p ∈ (N + 1).primesBelow, cofactorDifference p N) +
      (if P (N + 1) < P N then 1 else 0) := by
  rw [total_eq_prime_groups hN]
  have he : (∑ p ∈ (N + 1).primesBelow, group p N) =
      ∑ p ∈ (N + 1).primesBelow,
        (cofactorDifference p N + if P N = p ∧ P (N + 1) < p then 1 else 0) := by
    apply Finset.sum_congr rfl
    intro p hp
    exact group_eq_cofactorDifference (Nat.prime_of_mem_primesBelow hp) N
  rw [he, Finset.sum_add_distrib, endpoint_sum]
  ring

/-- Omitting the condition on the cofactor would wrongly assign this comparison to `p = 3`. -/
lemma cofactor_condition_necessary :
    P (5 * 3 + 1) < 3 ∧ 3 < P 5 ∧ P (5 * 3) ≠ 3 := by
  decide +kernel

open Filter
open scoped Topology

lemma endpoint_error_tendsto_zero :
    Tendsto (fun N : ℕ => (1 + if P (N + 1) < P N then (1 : ℝ) else 0) / N)
      atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (tendsto_const_div_atTop_nhds_zero_nat (2 : ℝ))
  · intro N
    positivity
  · intro N
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
    split_ifs <;> norm_num

lemma total_mean_eq_cofactor_mean_add {N : ℕ} (hN : 0 < N) :
    (total N : ℝ) / N =
      ((∑ p ∈ (N + 1).primesBelow, cofactorDifference p N : ℤ) : ℝ) / N +
      (1 + if P (N + 1) < P N then (1 : ℝ) else 0) / N := by
  rw [total_eq_cofactor_sum hN]
  push_cast
  split_ifs <;> push_cast <;> ring

lemma density_half_iff_cofactor_discrepancy :
    {n | P n < P (n + 1)}.HasDensity (1 / 2) ↔
      Tendsto (fun N : ℕ =>
        ((∑ p ∈ (N + 1).primesBelow, cofactorDifference p N : ℤ) : ℝ) / N)
        atTop (𝓝 0) := by
  rw [density_half_iff_total_mean_zero]
  constructor
  · intro h
    have hh := h.sub endpoint_error_tendsto_zero
    simp only [sub_zero] at hh
    apply hh.congr'
    filter_upwards [eventually_gt_atTop 0] with N hN
    rw [total_mean_eq_cofactor_mean_add hN]
    ring
  · intro h
    have hh := h.add endpoint_error_tendsto_zero
    simp only [add_zero] at hh
    apply hh.congr'
    filter_upwards [eventually_gt_atTop 0] with N hN
    exact (total_mean_eq_cofactor_mean_add hN).symm

end Erdos371CofactorDiscrepancy

#print axioms Erdos371CofactorDiscrepancy.group_eq_cofactorDifference

#print axioms Erdos371CofactorDiscrepancy.total_eq_cofactor_sum
#print axioms Erdos371CofactorDiscrepancy.density_half_iff_cofactor_discrepancy
