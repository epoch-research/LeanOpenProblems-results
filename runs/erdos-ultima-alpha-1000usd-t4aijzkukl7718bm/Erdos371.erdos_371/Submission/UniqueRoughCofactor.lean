import Submission.SubpowerBalanced

/-! A rough divisor with complementary factor at most the roughness cutoff
is unique. This improves the rectangular truncation error, but does not
estimate the remaining signed rectangle. -/

namespace Erdos371

lemma rough_divisor_eq_of_small_cofactors (B m a b : ℕ)
    (ha : a ∈ m.divisors) (hb : b ∈ m.divisors)
    (haB : B < a.minFac) (hbB : B < b.minFac)
    (hqa : m / a ≤ B) (hqb : m / b ≤ B) : a = b := by
  have ha' := (Nat.mem_divisors.mp ha).1
  have hb' := (Nat.mem_divisors.mp hb).1
  have hm : 0 < m := Nat.pos_of_ne_zero (Nat.mem_divisors.mp ha).2
  have hma := Nat.mul_div_cancel' ha'
  have hmb := Nat.mul_div_cancel' hb'
  have hqa0 : m / a ≠ 0 := by
    intro h
    rw [h, mul_zero] at hma
    omega
  have hqb0 : m / b ≠ 0 := by
    intro h
    rw [h, mul_zero] at hmb
    omega
  have hca : (m / a).Coprime b := (Nat.coprime_of_lt_minFac hqa0 (hqa.trans_lt hbB)).symm
  have hcb : (m / b).Coprime a := (Nat.coprime_of_lt_minFac hqb0 (hqb.trans_lt haB)).symm
  apply Nat.dvd_antisymm
  · apply hcb.symm.dvd_of_dvd_mul_right
    simpa only [hmb] using ha'
  · apply hca.symm.dvd_of_dvd_mul_right
    simpa only [hma] using hb'

lemma large_rough_divisor_card_le_one (B K N m : ℕ) (hm : m ≤ N + 1) (hKB : K ≤ B) :
    (m.divisors.filter fun a => N < K * a ∧ 1 < a ∧ B < a.minFac).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro a ha b hb
  obtain ⟨ha, hKa, ha1, haB⟩ := Finset.mem_filter.mp ha
  obtain ⟨hb, hKb, hb1, hbB⟩ := Finset.mem_filter.mp hb
  apply rough_divisor_eq_of_small_cofactors B m a b ha hb haB hbB
  · have hprod := Nat.mul_div_cancel' (Nat.mem_divisors.mp ha).1
    have hma : m ≤ K * a := by omega
    have hqa : m / a ≤ K := by nlinarith
    exact hqa.trans hKB
  · have hprod := Nat.mul_div_cancel' (Nat.mem_divisors.mp hb).1
    have hmb : m ≤ K * b := by omega
    have hqb : m / b ≤ K := by nlinarith
    exact hqb.trans hKB

lemma largeBilinearIntersection_unique_norm_le (B D K N n : ℕ)
    (hn : n ≤ N) (hKB : K ≤ B) :
    ‖largeBilinearIntersection B D K N n‖ ≤
      ((n.divisors.filter fun a => N < K * a ∧ 1 < a ∧ B < a.minFac).card : ℝ) := by
  have hc : (((n + 1).divisors.filter fun b => N < K * b).filter
      fun b => 1 < b ∧ B < b.minFac).card ≤ 1 := by
    simpa only [Finset.filter_filter] using
      large_rough_divisor_card_le_one B K N (n + 1) (by omega) hKB
  apply (roughBilinearWeight_rectangle_norm_le B D _ _).trans
  simp only [Finset.filter_filter] at hc ⊢
  simpa only [mul_one] using
    mul_le_mul_of_nonneg_left (show (↑(((n + 1).divisors.filter fun b =>
      N < K * b ∧ 1 < b ∧ B < b.minFac).card) : ℝ) ≤ 1 by exact_mod_cast hc)
      (show (0 : ℝ) ≤ (n.divisors.filter fun a =>
        N < K * a ∧ 1 < a ∧ B < a.minFac).card by positivity)

lemma largeBilinearIntersection_linear_prefix_bound (B D K N : ℕ) (hKB : K ≤ B) :
    ‖∑ n ∈ Finset.range N, largeBilinearIntersection B D K N (n + 1)‖ ≤
      (K : ℝ) * roughNumberCount B (N + 1) := by
  calc
    _ ≤ ∑ n ∈ Finset.range N, ‖largeBilinearIntersection B D K N (n + 1)‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.range N, (((n + 1).divisors.filter fun a =>
        N < K * a ∧ 1 < a ∧ B < a.minFac).card : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      exact largeBilinearIntersection_unique_norm_le B D K N (n + 1)
        (Finset.mem_range.mp hn) hKB
    _ ≤ _ := by exact_mod_cast fixed_cofactor_count_bound B K N

/-- Both coordinates can be truncated with a linear, rather than quadratic,
loss in the cofactor cutoff. -/
theorem balancedBilinearSum_linear_error_bound (B D K N : ℕ) (hD : D ≤ N) (hKB : K ≤ B) :
    ‖(∑ n ∈ Finset.range N, roughMixedDivisorTail B D (n + 1)) -
        ∑ n ∈ Finset.range N, balancedBilinearSum B D K N (n + 1)‖ ≤
      3 * (K + 1 : ℝ) * roughNumberCount B (N + 2) := by
  rw [← Finset.sum_sub_distrib]
  simp_rw [balanced_bilinear_decomposition B D K N _ (Nat.zero_lt_succ _)]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have hR := largeBilinearRows_prefix_bound B D K N hD (by omega)
  have hC := largeBilinearColumns_prefix_bound B D K N hD (by omega)
  have hI := largeBilinearIntersection_linear_prefix_bound B D K N hKB
  have hc : (roughNumberCount B (N + 1) : ℝ) ≤ roughNumberCount B (N + 2) := by
    exact_mod_cast roughNumberCount_mono_right B (show N + 1 ≤ N + 2 by omega)
  calc
    _ ≤ (‖∑ n ∈ Finset.range N, largeBilinearRows B D K N (n + 1)‖ +
        ‖∑ n ∈ Finset.range N, largeBilinearColumns B D K N (n + 1)‖) +
        ‖∑ n ∈ Finset.range N, largeBilinearIntersection B D K N (n + 1)‖ :=
      (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ ((K : ℝ) * roughNumberCount B (N + 1) +
        (K + 1 : ℝ) * roughNumberCount B (N + 2)) +
        (K : ℝ) * roughNumberCount B (N + 1) := add_le_add (add_le_add hR hC) hI
    _ ≤ ((K : ℝ) * roughNumberCount B (N + 2) +
        (K + 1 : ℝ) * roughNumberCount B (N + 2)) +
        (K : ℝ) * roughNumberCount B (N + 2) := by
      have h := mul_le_mul_of_nonneg_left hc (Nat.cast_nonneg K)
      exact add_le_add (add_le_add h le_rfl) h
    _ ≤ _ := by
      have hR0 : (0 : ℝ) ≤ roughNumberCount B (N + 2) := Nat.cast_nonneg _
      nlinarith

open Filter in
/-- A weaker sufficient error condition for the balanced reduction. The
zero-mean limit on the right remains a separate, unproved assertion. -/
theorem density_iff_balanced_of_linear_error (B K : ℕ → ℕ)
    (hB : Tendsto (fun N => Real.log (B N + 1 : ℝ) / Real.log N) atTop (nhds 0))
    (hKB : ∀ᶠ N in atTop, K N ≤ B N)
    (herror : Tendsto (fun N => (K N + 1 : ℝ) * roughNumberCount (B N) (N + 2) / N)
      atTop (nhds 0)) :
    ({n | Nat.maxPrimeFac (n + 1) > Nat.maxPrimeFac n}.HasDensity (1 / 2) ↔
      Tendsto (fun N : ℕ =>
        (∑ n ∈ Finset.range N,
          balancedBilinearSum (B N) (nearLinearCutoff N) (K N) N (n + 1)) / N)
        atTop (nhds 0)) := by
  have herr : Tendsto (fun N : ℕ =>
        ((∑ n ∈ Finset.range N,
          roughMixedDivisorTail (B N) (nearLinearCutoff N) (n + 1)) -
        ∑ n ∈ Finset.range N,
          balancedBilinearSum (B N) (nearLinearCutoff N) (K N) N (n + 1)) / N)
        atTop (nhds 0) := by
    have ht := herror.const_mul (3 : ℝ)
    simp only [mul_zero] at ht
    apply squeeze_zero_norm' _ ht
    filter_upwards [hKB] with N hKN
    rw [norm_div, Real.norm_natCast]
    calc
      _ ≤ (3 * (K N + 1 : ℝ) * roughNumberCount (B N) (N + 2)) / N :=
        div_le_div_of_nonneg_right (balancedBilinearSum_linear_error_bound _ _ _ _
          (nearLinearCutoff_le_self N) hKN) (Nat.cast_nonneg N)
      _ = _ := by ring
  rw [density_iff_subpower_rough_mixed_tail B hB]
  constructor
  · intro h
    have ht := h.sub herr
    simp only [sub_zero] at ht
    apply ht.congr
    intro N
    ring
  · intro h
    have ht := h.add herr
    simp only [add_zero] at ht
    apply ht.congr
    intro N
    ring

#print axioms rough_divisor_eq_of_small_cofactors
#print axioms large_rough_divisor_card_le_one
#print axioms balancedBilinearSum_linear_error_bound
#print axioms density_iff_balanced_of_linear_error
end Erdos371
