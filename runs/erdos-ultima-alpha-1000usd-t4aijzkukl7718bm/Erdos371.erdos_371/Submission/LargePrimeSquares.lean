import Submission.RoughPrimePart

/-! Prime-square divisibility above a growing cutoff is negligible, with a
uniform bound by the tail of the convergent series sum 1/d^2. -/

namespace Erdos371

noncomputable def largePrimeSquareCount (B N : ℕ) : ℕ := by
  classical
  exact ((Finset.range N).filter fun n => ∃ p, p.Prime ∧ B < p ∧ p^2 ∣ n + 1).card

lemma largePrimeSquareCount_bound (B N : ℕ) :
    (largePrimeSquareCount B N : ℝ) ≤
      N * (∑ p ∈ Finset.range (N + 1) with B < p, (1 : ℝ) / (p : ℝ)^2) := by
  classical
  have hpoint (n : ℕ) (hn : n ∈ Finset.range N) :
      (if ∃ p, p.Prime ∧ B < p ∧ p^2 ∣ n + 1 then (1 : ℝ) else 0) ≤
        ∑ p ∈ Finset.range (N + 1) with B < p, if p^2 ∣ n + 1 then (1 : ℝ) else 0 := by
    split_ifs with h
    · obtain ⟨p, hp, hpB, hpn⟩ := h
      have hpN : p ≤ N := by
        have hd := Nat.le_of_dvd (by omega : 0 < n + 1) hpn
        have hnN := Finset.mem_range.mp hn
        have hp2 := hp.two_le
        nlinarith
      have hmem : p ∈ (Finset.range (N + 1)).filter (B < ·) :=
        Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hpB⟩
      simpa only [if_pos hpn] using Finset.single_le_sum
        (fun q _ => by split_ifs <;> norm_num : ∀ q ∈ (Finset.range (N + 1)).filter (B < ·),
          (0 : ℝ) ≤ if q^2 ∣ n + 1 then 1 else 0) hmem
    · exact Finset.sum_nonneg fun p _ => by split_ifs <;> norm_num
  calc
    _ = ∑ n ∈ Finset.range N, if ∃ p, p.Prime ∧ B < p ∧ p^2 ∣ n + 1 then (1 : ℝ) else 0 := by
      simp [largePrimeSquareCount]
    _ ≤ ∑ n ∈ Finset.range N, ∑ p ∈ Finset.range (N + 1) with B < p,
        if p^2 ∣ n + 1 then (1 : ℝ) else 0 := Finset.sum_le_sum hpoint
    _ = ∑ p ∈ Finset.range (N + 1) with B < p, ((N / p^2 : ℕ) : ℝ) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro p hp
      simp [Nat.card_multiples]
    _ ≤ _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro p hp
      convert (Nat.cast_div_le (m := N) (n := p^2) (α := ℝ)) using 1 <;> push_cast <;> ring

lemma reciprocal_square_tail_bound (B N : ℕ) :
    (∑ p ∈ Finset.range (N + 1) with B < p, (1 : ℝ) / (p : ℝ)^2) ≤
      (∑' p : ℕ, (1 : ℝ) / (p : ℝ)^2) - ∑ p ∈ Finset.range (B + 1), (1 : ℝ) / (p : ℝ)^2 := by
  have hf : Summable (fun p : ℕ => (1 : ℝ) / (p : ℝ)^2) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  let S := (Finset.range (N + 1)).filter (B < ·)
  have hd : Disjoint S (Finset.range (B + 1)) := by
    apply Finset.disjoint_left.mpr
    intro p hp hpr
    have hpB := (Finset.mem_filter.mp hp).2
    have hprB := Finset.mem_range.mp hpr
    omega
  have h := Summable.sum_le_tsum (S ∪ Finset.range (B + 1)) (fun p _ => by positivity) hf
  rw [Finset.sum_union hd] at h
  linarith

lemma largePrimeSquareCount_ratio_bound (B N : ℕ) (hN : 0 < N) :
    (largePrimeSquareCount B N : ℝ) / N ≤
      (∑' p : ℕ, (1 : ℝ) / (p : ℝ)^2) - ∑ p ∈ Finset.range (B + 1), (1 : ℝ) / (p : ℝ)^2 := by
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  calc
    _ ≤ ((N : ℝ) * ∑ p ∈ Finset.range (N + 1) with B < p, (1 : ℝ) / (p : ℝ)^2) / N :=
      div_le_div_of_nonneg_right (largePrimeSquareCount_bound B N) (Nat.cast_nonneg N)
    _ = ∑ p ∈ Finset.range (N + 1) with B < p, (1 : ℝ) / (p : ℝ)^2 := by field_simp
    _ ≤ _ := reciprocal_square_tail_bound B N

open Filter in
theorem largePrimeSquareCount_tendsto_zero (B : ℕ → ℕ) (hB : Tendsto B atTop atTop) :
    Tendsto (fun N => (largePrimeSquareCount (B N) N : ℝ) / N) atTop (nhds 0) := by
  have hf : Summable (fun p : ℕ => (1 : ℝ) / (p : ℝ)^2) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  have ht := (hf.hasSum.tendsto_sum_nat.comp
    ((tendsto_add_atTop_nat 1).comp hB)).const_sub (∑' p : ℕ, (1 : ℝ) / (p : ℝ)^2)
  simp only [sub_self] at ht
  apply squeeze_zero_norm' _ ht
  filter_upwards [eventually_gt_atTop 0] with N hN
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact largePrimeSquareCount_ratio_bound (B N) N hN

lemma largePrimeSquareCount_succ_le (B N : ℕ) :
    largePrimeSquareCount B (N + 1) ≤ largePrimeSquareCount B N + 1 := by
  classical
  unfold largePrimeSquareCount
  rw [Finset.range_add_one, Finset.filter_insert]
  split_ifs
  · exact Finset.card_insert_le _ _
  · omega

open Filter in
theorem largePrimeSquareCount_succ_tendsto_zero (B : ℕ → ℕ) (hB : Tendsto B atTop atTop) :
    Tendsto (fun N => (largePrimeSquareCount (B N) (N + 1) : ℝ) / N) atTop (nhds 0) := by
  have ht := (largePrimeSquareCount_tendsto_zero B hB).add tendsto_one_div_atTop_nhds_zero_nat
  simp only [add_zero] at ht
  apply squeeze_zero (fun N => by positivity) _ ht
  intro N
  rw [← add_div]
  exact div_le_div_of_nonneg_right (by exact_mod_cast largePrimeSquareCount_succ_le (B N) N)
    (Nat.cast_nonneg N)

#print axioms largePrimeSquareCount_bound
#print axioms largePrimeSquareCount_tendsto_zero
#print axioms largePrimeSquareCount_succ_tendsto_zero
end Erdos371
