import Submission.TailExplore

/-! Exact cancellation of complete least-prime-factor groups.
In particular, an isolated Möbius-correlation term should not be confused
with the whole remainder: the entire even-divisor group cancels exactly. -/

namespace Erdos371

lemma leastFactorTerm_indicator (Q : ℕ → Prop) [DecidablePred Q] (f : ℕ → ℝ) (d : ℕ) :
    leastFactorTerm (fun p => if Q p then f p else 0) d =
      if Q d.minFac then leastFactorTerm f d else 0 := by
  unfold leastFactorTerm
  dsimp only
  split_ifs <;> ring

/-- Filtering by the least factor in the divisor expansion selects the
corresponding predicate of the largest factor in the result. -/
lemma alladi_divisors_filter (m : ℕ) (hm : 1 < m) (Q : ℕ → Prop) [DecidablePred Q]
    (f : ℕ → ℝ) :
    (∑ d ∈ m.divisors with Q d.minFac, leastFactorTerm f d) =
      if Q (Nat.maxPrimeFac m) then (∑ d ∈ m.divisors, leastFactorTerm f d) else 0 := by
  classical
  rw [Finset.sum_filter]
  simp_rw [← leastFactorTerm_indicator Q f]
  rw [alladi_divisors m hm, alladi_divisors m hm]
  split_ifs <;> simp

lemma orientedDivisorTerm_filter (n : ℕ) (hn : 0 < n) (Q : ℕ → Prop) [DecidablePred Q] :
    (∑ d ∈ (n * (n + 1)).divisors with Q d.minFac, orientedDivisorTerm d n) =
      if Q (Nat.maxPrimeFac (n * (n + 1))) then -factorSign n else 0 := by
  classical
  have he (s : Finset ℕ) (hs : s ⊆ (n * (n + 1)).divisors) :
      (∑ d ∈ s, orientedDivisorTerm d n) =
        ∑ d ∈ s, leastFactorTerm (fun p => if p ∣ n + 1 then 1 else -1) d := by
    apply Finset.sum_congr rfl
    intro d hd
    simp only [orientedDivisorTerm, if_pos (Nat.mem_divisors.mp (hs hd)).1]
  rw [he _ (Finset.filter_subset _ _), alladi_divisors_filter _ (by nlinarith),
    ← he _ (Finset.Subset.refl _), sum_orientedDivisorTerm n hn]

/-- For n ≥ 2, the product n(n+1) has a prime factor greater than two. -/
lemma maxPrimeFac_consecutive_product_gt_two (n : ℕ) (hn : 2 ≤ n) :
    2 < Nat.maxPrimeFac (n * (n + 1)) := by
  have hp := (Nat.prime_maxPrimeFac_of_one_lt n (by omega)).two_le
  have hq := (Nat.prime_maxPrimeFac_of_one_lt (n + 1) (by omega)).two_le
  have hne := consecutive_maxPrimeFac_ne n
  rw [Nat.maxPrimeFac_mul (by omega) (by omega)]
  omega

/-- This includes the top divisor's alternating Möbius correlation, but the
whole even-divisor group is zero pointwise for every n ≥ 2. -/
theorem even_oriented_divisor_group_zero (n : ℕ) (hn : 2 ≤ n) :
    (∑ d ∈ (n * (n + 1)).divisors with 2 ∣ d, orientedDivisorTerm d n) = 0 := by
  have h := orientedDivisorTerm_filter n (by omega) (fun p => p = 2)
  simpa only [Nat.minFac_eq_two_iff, if_neg (maxPrimeFac_consecutive_product_gt_two n hn).ne'] using h

noncomputable def lowLeastDivisorGroup (B n : ℕ) : ℝ :=
  ∑ d ∈ (n * (n + 1)).divisors with d.minFac ≤ B, orientedDivisorTerm d n

lemma lowLeastDivisorGroup_eq (B n : ℕ) (hn : 0 < n) :
    lowLeastDivisorGroup B n =
      if Nat.maxPrimeFac (n * (n + 1)) ≤ B then -factorSign n else 0 :=
  orientedDivisorTerm_filter n hn (fun p => p ≤ B)

@[simp] lemma lowLeastDivisorGroup_zero (B : ℕ) : lowLeastDivisorGroup B 0 = 0 := by
  simp [lowLeastDivisorGroup]

lemma lowLeastDivisorGroup_vanishes (B n : ℕ) (hn : 0 < n)
    (hB : B < Nat.maxPrimeFac (n * (n + 1))) : lowLeastDivisorGroup B n = 0 := by
  rw [lowLeastDivisorGroup_eq B n hn, if_neg (not_le.mpr hB)]

lemma lowLeastDivisorGroup_norm_le_indicator (B n : ℕ) :
    ‖lowLeastDivisorGroup B n‖ ≤ if Nat.maxPrimeFac n ≤ B then (1 : ℝ) else 0 := by
  by_cases hn : n = 0
  · simp [hn]
  · rw [lowLeastDivisorGroup_eq B n (Nat.pos_of_ne_zero hn)]
    by_cases hm : Nat.maxPrimeFac (n * (n + 1)) ≤ B
    · have hB : Nat.maxPrimeFac n ≤ B := by
        rw [Nat.maxPrimeFac_mul hn (by omega)] at hm
        exact (le_max_left _ _).trans hm
      simp only [if_pos hm, if_pos hB, norm_neg, factorSign_norm, le_refl]
    · simp only [if_neg hm, norm_zero]
      split_ifs <;> norm_num

lemma lowLeastDivisorGroup_norm_le_one (B n : ℕ) : ‖lowLeastDivisorGroup B n‖ ≤ 1 := by
  apply (lowLeastDivisorGroup_norm_le_indicator B n).trans
  split_ifs <;> norm_num

open Filter in
/-- Every fixed bounded range of least prime factors has zero average,
including all its arbitrarily large divisors. -/
theorem lowLeastDivisorGroup_average_zero (B : ℕ) :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, lowLeastDivisorGroup B n) / N)
      atTop (nhds 0) := by
  have ht := (density_iff_count (fun n => Nat.maxPrimeFac n ≤ B) 0).mp
    (bounded_maxPrimeFac_hasDensity_zero B)
  apply squeeze_zero_norm (a := fun N : ℕ =>
    (((Finset.range N).filter fun n => Nat.maxPrimeFac n ≤ B).card : ℝ) / N) _ ht
  intro N
  rw [norm_div, Real.norm_natCast]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
  calc
    _ ≤ ∑ n ∈ Finset.range N, ‖lowLeastDivisorGroup B n‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.range N, (if Nat.maxPrimeFac n ≤ B then (1 : ℝ) else 0) :=
      Finset.sum_le_sum fun n _ => lowLeastDivisorGroup_norm_le_indicator B n
    _ = _ := by simp

open Filter in
theorem lowLeastDivisorGroup_shifted_average_zero (B : ℕ) :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, lowLeastDivisorGroup B (n + 1)) / N)
      atTop (nhds 0) := by
  have he (N : ℕ) :
      (∑ n ∈ Finset.range N, lowLeastDivisorGroup B (n + 1)) =
        (∑ n ∈ Finset.range N, lowLeastDivisorGroup B n) + lowLeastDivisorGroup B N := by
    have h := Finset.sum_range_succ' (lowLeastDivisorGroup B) N
    rw [Finset.sum_range_succ] at h
    simpa only [lowLeastDivisorGroup_zero, add_zero] using h.symm
  have ht : Tendsto (fun N : ℕ => lowLeastDivisorGroup B N / N) atTop (nhds 0) := by
    apply squeeze_zero_norm (a := fun N : ℕ => (1 : ℝ) / N) _ tendsto_one_div_atTop_nhds_zero_nat
    intro N
    rw [norm_div, Real.norm_natCast]
    exact div_le_div_of_nonneg_right (lowLeastDivisorGroup_norm_le_one B N) (Nat.cast_nonneg N)
  have h := (lowLeastDivisorGroup_average_zero B).add ht
  simpa only [he, add_div, zero_add] using h

#print axioms orientedDivisorTerm_filter
#print axioms even_oriented_divisor_group_zero
#print axioms lowLeastDivisorGroup_shifted_average_zero

end Erdos371
