import FormalConjecturesUtil

/-! The signed comparison count, decomposed by its winning prime.
No cancellation estimate for the resulting prime sum is asserted here. -/

namespace Erdos371PrimeDiscrepancy

abbrev P := Nat.maxPrimeFac

def sign (n : ℕ) : ℤ := if P n < P (n + 1) then 1 else -1

def winner (n : ℕ) : ℕ := max (P n) (P (n + 1))

def total (N : ℕ) : ℤ := ∑ n ∈ Finset.range N, sign n

def group (p N : ℕ) : ℤ :=
  ∑ n ∈ Finset.range N, if winner n = p then sign n else 0

lemma winner_le {n N : ℕ} (hn : n < N) : winner n ≤ N := by
  have h1 := Nat.maxPrimeFac_le (n := n)
  have h2 := Nat.maxPrimeFac_le (n := n + 1)
  unfold winner P
  omega

lemma winner_prime {n : ℕ} (hn : 0 < n) : (winner n).Prime := by
  by_cases h : P n ≤ P (n + 1)
  · rw [winner, max_eq_right h]
    exact Nat.prime_maxPrimeFac_of_one_lt (n + 1) (by omega)
  · rw [winner, max_eq_left (Nat.le_of_not_ge h)]
    apply Nat.prime_maxPrimeFac_of_one_lt
    by_contra hn'
    have he : n = 1 := by omega
    subst n
    have hsmall : P 1 ≤ P 2 := by decide +kernel
    exact h hsmall

lemma total_eq_groups (N : ℕ) :
    total N = ∑ p ∈ Finset.range (N + 1), group p N := by
  unfold total group
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  have hw : winner n ∈ Finset.range (N + 1) :=
    Finset.mem_range.mpr (Nat.lt_succ_of_le (winner_le (Finset.mem_range.mp hn)))
  simp [hw]

lemma total_eq_prime_groups {N : ℕ} (hN : 0 < N) :
    total N = 1 + ∑ p ∈ (N + 1).primesBelow, group p N := by
  unfold group
  rw [Finset.sum_comm]
  have hs (n : ℕ) (hn : n ∈ Finset.range N) :
      (∑ p ∈ (N + 1).primesBelow, if winner n = p then sign n else 0) =
        if n = 0 then 0 else sign n := by
    by_cases hn0 : n = 0
    · subst n
      have hw : winner 0 = 1 := by decide +kernel
      have hp : 1 ∉ (N + 1).primesBelow := by simp [Nat.mem_primesBelow]
      simp [hw, hp]
    · have hw : winner n ∈ (N + 1).primesBelow :=
        Nat.mem_primesBelow.mpr
          ⟨Nat.lt_succ_of_le (winner_le (Finset.mem_range.mp hn)), winner_prime (by omega)⟩
      simp [hw, hn0]
  simp_rw [Finset.sum_congr rfl hs]
  unfold total
  have he (n : ℕ) : sign n = (if n = 0 then 1 else 0) + (if n = 0 then 0 else sign n) := by
    by_cases hn : n = 0
    · subst n
      decide +kernel
    · simp [hn]
  conv_lhs => arg 2; ext n; rw [he]
  rw [Finset.sum_add_distrib]
  have hz : 0 ∈ Finset.range N := Finset.mem_range.mpr hN
  simp [hz]

lemma total_eq_count (N : ℕ) :
    total N = 2 * (((Finset.range N).filter (fun n => P n < P (n + 1))).card : ℤ) - N := by
  have hs (n : ℕ) : sign n = 2 * (if P n < P (n + 1) then (1 : ℤ) else 0) - 1 := by
    unfold sign
    split_ifs <;> norm_num
  simp only [total, hs, Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp

open Filter
open scoped Topology

lemma partialDensity_eq_total {N : ℕ} (hN : N ≠ 0) :
    {n | P n < P (n + 1)}.partialDensity Set.univ N =
      ((total N : ℝ) / N + 1) / 2 := by
  have he : {n | P n < P (n + 1)} ∩ Set.Iio N =
      ↑((Finset.range N).filter (fun n => P n < P (n + 1))) := by
    ext n
    simp [and_comm]
  simp only [Set.partialDensity, Set.inter_univ, Set.univ_inter, Nat.ncard_Iio,
    he, Set.ncard_coe_finset]
  have ht : (total N : ℝ) =
      2 * (((Finset.range N).filter (fun n => P n < P (n + 1))).card : ℝ) - N := by
    exact_mod_cast total_eq_count N
  rw [ht]
  have hn : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  field_simp
  ring

lemma density_half_iff_total_mean_zero :
    {n | P n < P (n + 1)}.HasDensity (1 / 2) ↔
      Tendsto (fun N : ℕ => (total N : ℝ) / N) atTop (𝓝 0) := by
  constructor
  · intro h
    have hh : Tendsto (fun N : ℕ =>
        2 * {n | P n < P (n + 1)}.partialDensity Set.univ N - 1)
        atTop (𝓝 (2 * (1 / 2 : ℝ) - 1)) :=
      (tendsto_const_nhds.mul h).sub tendsto_const_nhds
    norm_num at hh
    apply hh.congr'
    filter_upwards [eventually_gt_atTop 0] with N hN
    have hd := partialDensity_eq_total (Nat.ne_of_gt hN)
    linarith
  · intro h
    have hh : Tendsto (fun N : ℕ => ((total N : ℝ) / N + 1) / 2)
        atTop (𝓝 (1 / 2 : ℝ)) := by
      convert (h.add tendsto_const_nhds).div_const (2 : ℝ) using 1; norm_num
    apply hh.congr'
    filter_upwards [eventually_gt_atTop 0] with N hN
    exact (partialDensity_eq_total (Nat.ne_of_gt hN)).symm


lemma prime_mean_eq_total_mean_sub {N : ℕ} (hN : 0 < N) :
    ((∑ p ∈ (N + 1).primesBelow, group p N : ℤ) : ℝ) / N =
      (total N : ℝ) / N - 1 / N := by
  rw [total_eq_prime_groups hN]
  push_cast
  ring

lemma density_half_iff_prime_discrepancy :
    {n | P n < P (n + 1)}.HasDensity (1 / 2) ↔
      Tendsto (fun N : ℕ =>
        ((∑ p ∈ (N + 1).primesBelow, group p N : ℤ) : ℝ) / N) atTop (𝓝 0) := by
  rw [density_half_iff_total_mean_zero]
  constructor
  · intro h
    have hh := h.sub tendsto_one_div_atTop_nhds_zero_nat
    simp only [sub_zero] at hh
    apply hh.congr'
    filter_upwards [eventually_gt_atTop 0] with N hN
    exact (prime_mean_eq_total_mean_sub hN).symm
  · intro h
    have hh := h.add tendsto_one_div_atTop_nhds_zero_nat
    simp only [add_zero] at hh
    apply hh.congr'
    filter_upwards [eventually_gt_atTop 0] with N hN
    rw [prime_mean_eq_total_mean_sub hN]
    ring

lemma consecutive_ne (n : ℕ) : P (n + 1) ≠ P n := by
  rcases n with _ | _ | n
  · simp [P]
  · decide +kernel
  · intro h
    have hp := Nat.prime_maxPrimeFac_of_one_lt (n + 2) (by omega)
    have hd : P (n + 2) ∣ n + 2 + 1 := by
      rw [← h]
      exact Nat.maxPrimeFac_dvd
    exact hp.not_dvd_one ((Nat.dvd_add_iff_right Nat.maxPrimeFac_dvd).2 hd)

lemma group_eq_counts (p N : ℕ) :
    group p N =
      (((Finset.range N).filter (fun n => P (n + 1) = p ∧ P n < p)).card : ℤ) -
      (((Finset.range N).filter (fun n => P n = p ∧ P (n + 1) < p)).card : ℤ) := by
  have he (n : ℕ) : (if winner n = p then sign n else 0) =
      (if P (n + 1) = p ∧ P n < p then (1 : ℤ) else 0) -
      (if P n = p ∧ P (n + 1) < p then (1 : ℤ) else 0) := by
    have hn := consecutive_ne n
    unfold winner sign
    simp only [max_def]
    split_ifs <;> omega
  simp only [group, he, Finset.sum_sub_distrib]
  simp

lemma prime_multiple_iff {p k : ℕ} (hp : p.Prime) (hk : 0 < k) :
    P (k * p) = p ↔ P k ≤ p := by
  rw [P, Nat.maxPrimeFac_mul hk.ne' hp.ne_zero, hp.maxPrimeFac_eq_self]
  exact max_eq_right_iff

lemma maxPrimeFac_eq_prime_below_twice {m p : ℕ} (hp : p.Prime) (hm : m < 2 * p) :
    P m = p ↔ m = p := by
  constructor
  · intro he
    have hd : p ∣ m := he ▸ Nat.maxPrimeFac_dvd
    obtain ⟨k, hk⟩ := hd
    have hk2 : k < 2 := by nlinarith [hp.pos]
    have hk0 : k ≠ 0 := by
      intro h0
      have hm0 : m = 0 := by simp [h0] at hk; exact hk
      simp [hm0, P] at he
      exact hp.ne_zero he.symm
    have hk1 : k = 1 := by omega
    simpa [hk1] using hk
  · rintro rfl
    exact hp.maxPrimeFac_eq_self

lemma after_odd_prime {p : ℕ} (hp : p.Prime) (hp2 : 2 < p) : P (p + 1) < p := by
  have heven : Even (p + 1) := (hp.odd_of_ne_two (by omega)).add_odd odd_one
  have hnot : ¬(p + 1).Prime := by
    intro h
    have := h.even_iff.mp heven
    omega
  have hne : P (p + 1) ≠ p + 1 := by
    simp only [P, ne_eq, Nat.maxPrimeFac_eq_self_iff, hnot, or_false]
    omega
  have hle : P (p + 1) ≤ p + 1 := Nat.maxPrimeFac_le
  have hdiff := consecutive_ne p
  rw [show P p = p from hp.maxPrimeFac_eq_self] at hdiff
  omega

/-- In this range the prime occurs only once, and the two comparisons around it cancel
unless the prime is exactly at the right endpoint of the counting interval. -/
lemma group_above_half {p N : ℕ} (hp : p.Prime) (hp2 : 2 < p) (hN : N < 2 * p) :
    group p N = if p = N then 1 else 0 := by
  have hu : (Finset.range N).filter (fun n => P (n + 1) = p ∧ P n < p) =
      (Finset.range N).filter (fun n => n = p - 1) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨hn, he, _⟩
      have hnp : n + 1 = p :=
        (maxPrimeFac_eq_prime_below_twice hp (by omega)).mp he
      exact ⟨hn, by omega⟩
    · rintro ⟨hn, rfl⟩
      have he : p - 1 + 1 = p := by omega
      refine ⟨hn, ?_, ?_⟩
      · rw [he]
        exact hp.maxPrimeFac_eq_self
      · exact Nat.maxPrimeFac_le.trans_lt (by omega)
  have hd : (Finset.range N).filter (fun n => P n = p ∧ P (n + 1) < p) =
      (Finset.range N).filter (fun n => n = p) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨hn, he, _⟩
      exact ⟨hn, (maxPrimeFac_eq_prime_below_twice hp (by omega)).mp he⟩
    · rintro ⟨hn, rfl⟩
      exact ⟨hn, hp.maxPrimeFac_eq_self, after_odd_prime hp hp2⟩
  rw [group_eq_counts, hu, hd]
  simp only [Finset.filter_eq', Finset.mem_range]
  split_ifs <;> simp_all <;> omega

end Erdos371PrimeDiscrepancy

#print axioms Erdos371PrimeDiscrepancy.total_eq_prime_groups

#print axioms Erdos371PrimeDiscrepancy.density_half_iff_prime_discrepancy
#print axioms Erdos371PrimeDiscrepancy.group_eq_counts

#print axioms Erdos371PrimeDiscrepancy.group_above_half
