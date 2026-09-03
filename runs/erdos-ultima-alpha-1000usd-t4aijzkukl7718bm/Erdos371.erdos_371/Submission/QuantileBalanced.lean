import Submission.HarmonicCofactorCutoff
import Submission.UniqueRoughCofactor

/-! A structured two-coordinate cutoff, controlled by a second-moment
sieve rather than a factor of K times a rough-number count. -/

namespace Erdos371

lemma rough_divisor_avoids_medium (B K m a : ℕ) (ha : a ∈ m.divisors)
    (haB : B < a.minFac) (hqa : m / a ≤ K) :
    ∀ p ∈ mediumPrimes K B, ¬p ∣ m := by
  intro p hp hpm
  obtain ⟨hp, hpK, hpB⟩ := mem_mediumPrimes.mp hp
  have hprod := Nat.mul_div_cancel' (Nat.mem_divisors.mp ha).1
  have hm : 0 < m := Nat.pos_of_ne_zero (Nat.mem_divisors.mp ha).2
  have hq : 0 < (m / a : ℕ) :=
    Nat.div_pos (Nat.le_of_dvd hm (Nat.mem_divisors.mp ha).1) (Nat.pos_of_mem_divisors ha)
  rw [← hprod] at hpm
  rcases hp.dvd_mul.mp hpm with hpa | hpq
  · have hmin := Nat.minFac_le_of_dvd hp.two_le hpa
    omega
  · have hle := Nat.le_of_dvd hq hpq
    omega

lemma large_rough_divisor_card_le_avoid (B K N m : ℕ) (hm : m ≤ N + 1) (hKB : K ≤ B) :
    (m.divisors.filter fun a => N < K * a ∧ 1 < a ∧ B < a.minFac).card ≤
      if ∀ p ∈ mediumPrimes K B, ¬p ∣ m then 1 else 0 := by
  split_ifs with h
  · exact large_rough_divisor_card_le_one B K N m hm hKB
  · apply Nat.le_zero.mpr
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro a ha
    obtain ⟨ha, hNa, ha1, haB⟩ := Finset.mem_filter.mp ha
    have hprod := Nat.mul_div_cancel' (Nat.mem_divisors.mp ha).1
    have hma : m ≤ K * a := by omega
    have hq : m / a ≤ K := by nlinarith
    exact h (rough_divisor_avoids_medium B K m a ha haB hq)

lemma primeAvoidCount_mono (S : Finset ℕ) {N M : ℕ} (hNM : N ≤ M) :
    primeAvoidCount S N ≤ primeAvoidCount S M :=
  Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_mono hNM))

lemma largeBilinearRows_medium_prefix_bound (B D K N : ℕ) (hD : D ≤ N) (hKB : K ≤ B) :
    ‖∑ n ∈ Finset.range N, largeBilinearRows B D K N (n + 1)‖ ≤
      primeAvoidCount (mediumPrimes K B) N := by
  calc
    _ ≤ ∑ n ∈ Finset.range N, ‖largeBilinearRows B D K N (n + 1)‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.range N,
        if ∀ p ∈ mediumPrimes K B, ¬p ∣ n + 1 then (1 : ℝ) else 0 := by
      apply Finset.sum_le_sum
      intro n hn
      apply (largeBilinearRows_norm_le B D K N (n + 1) hD (by omega)).trans
      have h := large_rough_divisor_card_le_avoid B K N (n + 1)
        (by have := Finset.mem_range.mp hn; omega) hKB
      exact_mod_cast h
    _ = _ := by simp [primeAvoidCount]

lemma largeBilinearColumns_medium_prefix_bound (B D K N : ℕ) (hD : D ≤ N) (hKB : K ≤ B) :
    ‖∑ n ∈ Finset.range N, largeBilinearColumns B D K N (n + 1)‖ ≤
      primeAvoidCount (mediumPrimes K B) (N + 1) := by
  calc
    _ ≤ ∑ n ∈ Finset.range N, ‖largeBilinearColumns B D K N (n + 1)‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.range N,
        if ∀ p ∈ mediumPrimes K B, ¬p ∣ n + 2 then (1 : ℝ) else 0 := by
      apply Finset.sum_le_sum
      intro n hn
      apply (largeBilinearColumns_norm_le B D K N (n + 1) hD (by omega)).trans
      have h := large_rough_divisor_card_le_avoid B K N (n + 2)
        (by have := Finset.mem_range.mp hn; omega) hKB
      exact_mod_cast h
    _ ≤ ∑ n ∈ Finset.range (N + 1),
        if ∀ p ∈ mediumPrimes K B, ¬p ∣ n + 1 then (1 : ℝ) else 0 := by
      rw [Finset.sum_range_succ']
      simp only [Nat.add_assoc, Nat.reduceAdd]
      exact le_add_of_nonneg_right (by split_ifs <;> norm_num)
    _ = _ := by simp [primeAvoidCount]

lemma largeBilinearIntersection_medium_prefix_bound (B D K N : ℕ) (hKB : K ≤ B) :
    ‖∑ n ∈ Finset.range N, largeBilinearIntersection B D K N (n + 1)‖ ≤
      primeAvoidCount (mediumPrimes K B) N := by
  calc
    _ ≤ ∑ n ∈ Finset.range N, ‖largeBilinearIntersection B D K N (n + 1)‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.range N,
        if ∀ p ∈ mediumPrimes K B, ¬p ∣ n + 1 then (1 : ℝ) else 0 := by
      apply Finset.sum_le_sum
      intro n hn
      apply (largeBilinearIntersection_unique_norm_le B D K N (n + 1)
        (Finset.mem_range.mp hn) hKB).trans
      have h := large_rough_divisor_card_le_avoid B K N (n + 1)
        (by have := Finset.mem_range.mp hn; omega) hKB
      exact_mod_cast h
    _ = _ := by simp [primeAvoidCount]

/-- The entire two-coordinate truncation error is supported on integers
avoiding the intervening primes. In particular, there is no factor K. -/
theorem balancedBilinearSum_medium_error_bound (B D K N : ℕ) (hD : D ≤ N) (hKB : K ≤ B) :
    ‖(∑ n ∈ Finset.range N, roughMixedDivisorTail B D (n + 1)) -
        ∑ n ∈ Finset.range N, balancedBilinearSum B D K N (n + 1)‖ ≤
      3 * primeAvoidCount (mediumPrimes K B) (N + 1) := by
  rw [← Finset.sum_sub_distrib]
  simp_rw [balanced_bilinear_decomposition B D K N _ (Nat.zero_lt_succ _)]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have hR := largeBilinearRows_medium_prefix_bound B D K N hD hKB
  have hC := largeBilinearColumns_medium_prefix_bound B D K N hD hKB
  have hI := largeBilinearIntersection_medium_prefix_bound B D K N hKB
  have hc : (primeAvoidCount (mediumPrimes K B) N : ℝ) ≤
      primeAvoidCount (mediumPrimes K B) (N + 1) := by
    exact_mod_cast primeAvoidCount_mono (mediumPrimes K B) (show N ≤ N + 1 by omega)
  calc
    _ ≤ (‖∑ n ∈ Finset.range N, largeBilinearRows B D K N (n + 1)‖ +
        ‖∑ n ∈ Finset.range N, largeBilinearColumns B D K N (n + 1)‖) +
        ‖∑ n ∈ Finset.range N, largeBilinearIntersection B D K N (n + 1)‖ :=
      (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ (primeAvoidCount (mediumPrimes K B) (N + 1) : ℝ) +
        primeAvoidCount (mediumPrimes K B) (N + 1) +
        primeAvoidCount (mediumPrimes K B) (N + 1) :=
      add_le_add (add_le_add (hR.trans hc) hC) (hI.trans hc)
    _ = _ := by ring

/-- A finite quantitative version: with the harmonic-quantile cutoff, the
normalized truncation error is at most 36 divided by the prime harmonic mass. -/
theorem balancedBilinearSum_quantile_error_ratio_le (B D N : ℕ)
    (hD : D ≤ N) (hBN : B ≤ N) (hN : 0 < N) (hB : 0 < primeHarmonic B) :
    ‖((∑ n ∈ Finset.range N, roughMixedDivisorTail B D (n + 1)) -
        ∑ n ∈ Finset.range N,
          balancedBilinearSum B D (harmonicCofactorCutoff B) N (n + 1)) / N‖ ≤
      36 / primeHarmonic B := by
  let S := mediumPrimes (harmonicCofactorCutoff B) B
  have hmass : primeHarmonic B / 2 ≤ primeReciprocalSum S :=
    harmonicCofactorCutoff_remaining_mass B
  have hH : 0 < primeReciprocalSum S := (half_pos hB).trans_le hmass
  have hc := primeAvoidCount_mul_reciprocal_le S (N + 1)
    (fun p hp => (mem_mediumPrimes.mp hp).1) hH
  have hcard : (S.card : ℝ) ≤ N + 1 := by
    exact_mod_cast (mediumPrimes_card_le (harmonicCofactorCutoff B) B).trans
      (show B + 1 ≤ N + 1 by omega)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hc0 : (0 : ℝ) ≤ primeAvoidCount S (N + 1) := Nat.cast_nonneg _
  simp only [Nat.cast_add, Nat.cast_one] at hc
  have hcH : (primeAvoidCount S (N + 1) : ℝ) * primeHarmonic B ≤ 12 * N := by
    nlinarith [mul_le_mul_of_nonneg_left hmass hc0]
  have he := balancedBilinearSum_medium_error_bound B D (harmonicCofactorCutoff B) N hD
    (harmonicCofactorCutoff_le B)
  rw [norm_div, Real.norm_natCast]
  apply (le_div_iff₀ hB).mpr
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hN0).mpr
  have heH := mul_le_mul_of_nonneg_right he hB.le
  change _ ≤ 3 * (primeAvoidCount S (N + 1) : ℝ) * primeHarmonic B at heH
  nlinarith

open Filter in
/-- The harmonic-quantile cofactor cutoff is now fixed by B, rather than
chosen by an abstract slow-cutoff argument. The rectangle's limit is still
unproved. -/
theorem density_iff_quantile_balanced (B : ℕ → ℕ)
    (hBatTop : Tendsto B atTop atTop)
    (hB : Tendsto (fun N => Real.log (B N + 1 : ℝ) / Real.log N) atTop (nhds 0)) :
    ({n | Nat.maxPrimeFac (n + 1) > Nat.maxPrimeFac n}.HasDensity (1 / 2) ↔
      Tendsto (fun N : ℕ =>
        (∑ n ∈ Finset.range N,
          balancedBilinearSum (B N) (nearLinearCutoff N) (harmonicCofactorCutoff (B N)) N (n + 1)) / N)
        atTop (nhds 0)) := by
  have herr : Tendsto (fun N : ℕ =>
        ((∑ n ∈ Finset.range N,
          roughMixedDivisorTail (B N) (nearLinearCutoff N) (n + 1)) -
        ∑ n ∈ Finset.range N,
          balancedBilinearSum (B N) (nearLinearCutoff N) (harmonicCofactorCutoff (B N)) N (n + 1)) / N)
        atTop (nhds 0) := by
    have ht := (harmonicCofactorCutoff_avoid_count_succ_tendsto B hBatTop
      (subpower_cutoff_eventually_le B hB)).const_mul (3 : ℝ)
    simp only [mul_zero] at ht
    apply squeeze_zero_norm' _ ht
    filter_upwards [] with N
    rw [norm_div, Real.norm_natCast]
    calc
      _ ≤ ((3 : ℝ) * primeAvoidCount (mediumPrimes (harmonicCofactorCutoff (B N)) (B N)) (N + 1)) / N :=
        div_le_div_of_nonneg_right (balancedBilinearSum_medium_error_bound _ _ _ _
          (nearLinearCutoff_le_self N) (harmonicCofactorCutoff_le (B N))) (Nat.cast_nonneg N)
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

open Filter in
theorem density_iff_subpower_quantile_balanced :
    ({n | Nat.maxPrimeFac (n + 1) > Nat.maxPrimeFac n}.HasDensity (1 / 2) ↔
      Tendsto (fun N : ℕ =>
        (∑ n ∈ Finset.range N,
          balancedBilinearSum (subpowerCutoff N) (nearLinearCutoff N)
            (harmonicCofactorCutoff (subpowerCutoff N)) N (n + 1)) / N)
        atTop (nhds 0)) :=
  density_iff_quantile_balanced subpowerCutoff subpowerCutoff_atTop
    subpowerCutoff_log_ratio_tendsto_zero

#print axioms rough_divisor_avoids_medium
#print axioms balancedBilinearSum_medium_error_bound
#print axioms balancedBilinearSum_quantile_error_ratio_le
#print axioms density_iff_quantile_balanced
#print axioms density_iff_subpower_quantile_balanced
end Erdos371
