import Submission.Comparison

/-!
# Conditional density reduction for consecutive greatest-prime-factor comparisons

For an arbitrary set of natural numbers, its signed indicator has partial sum
`2 * countBelow - N`. Consequently, density `d` is equivalent to convergence of
the normalized signed sum to `2 * d - 1`.

We specialize this equivalence to the exact set
`{n : ℕ | Nat.maxPrimeFac (n + 1) > Nat.maxPrimeFac n}`. The sums use `range N`,
so the ascending comparisons at zero and one are included, not discarded.

This is only a conditional reduction: no convergence or density assertion for
this prime-factor comparison set is proved or assumed here. In particular, this
file does not import `Submission.Spec` or the original conjecture theorem.
-/

open Filter
open scoped Topology

namespace DensityReduction

/-- The signed indicator of an arbitrary set of natural numbers. -/
noncomputable def signedIndicator (A : Set ℕ) (n : ℕ) : ℤ :=
  open scoped Classical in
  if n ∈ A then 1 else -1

/-- The number of members of `A` strictly below `N`, including zero when present. -/
noncomputable def countBelow (A : Set ℕ) (N : ℕ) : ℕ :=
  open scoped Classical in
  ((Finset.range N).filter (fun n => n ∈ A)).card

/-- The total signed-indicator sum on exactly the first `N` natural numbers. -/
noncomputable def signedSum (A : Set ℕ) (N : ℕ) : ℤ :=
  ∑ n ∈ Finset.range N, signedIndicator A n

/-- The signed sum divided by `N`, with division in `ℝ`. -/
noncomputable def normalizedSignedSum (A : Set ℕ) (N : ℕ) : ℝ :=
  (signedSum A N : ℝ) / N

/-- The finset count is exactly the set cardinality used in natural density. -/
theorem countBelow_eq_ncard (A : Set ℕ) (N : ℕ) :
    countBelow A N = (A ∩ Set.Iio N).ncard := by
  classical
  unfold countBelow
  rw [← Set.ncard_coe_finset]
  congr 1
  ext n
  simp [and_comm]

/-- Exact signed-count identity, valid also at `N = 0` (all arithmetic is in `ℤ`). -/
theorem signedSum_eq_two_mul_countBelow_sub (A : Set ℕ) (N : ℕ) :
    signedSum A N = 2 * (countBelow A N : ℤ) - (N : ℤ) := by
  classical
  calc
    signedSum A N =
        ∑ n ∈ Finset.range N, (2 * (if n ∈ A then (1 : ℤ) else 0) - 1) := by
      unfold signedSum
      apply Finset.sum_congr rfl
      intro n _
      by_cases hn : n ∈ A <;> simp [signedIndicator, hn]
    _ = 2 * (countBelow A N : ℤ) - (N : ℤ) := by
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
      simp [countBelow]

/-- The exact identity expressed directly using `Set.ncard` and `Finset.range`. -/
theorem sum_signedIndicator_eq_two_mul_ncard_sub (A : Set ℕ) (N : ℕ) :
    (∑ n ∈ Finset.range N, signedIndicator A n) =
      2 * ((A ∩ Set.Iio N).ncard : ℤ) - (N : ℤ) := by
  simpa only [signedSum, countBelow_eq_ncard] using
    signedSum_eq_two_mul_countBelow_sub A N

/-- Natural partial density is the exact prefix count divided by `N`. -/
theorem partialDensity_eq_countBelow_div (A : Set ℕ) (N : ℕ) :
    A.partialDensity Set.univ N = (countBelow A N : ℝ) / N := by
  simp [Set.partialDensity, countBelow_eq_ncard]

/-- Away from the zero denominator, the normalized signed sum is `2*density - 1`. -/
theorem normalizedSignedSum_eq (A : Set ℕ) {N : ℕ} (hN : 0 < N) :
    normalizedSignedSum A N = 2 * A.partialDensity Set.univ N - 1 := by
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)
  rw [normalizedSignedSum, signedSum_eq_two_mul_countBelow_sub,
    partialDensity_eq_countBelow_div]
  push_cast
  field_simp

/-- The affine relation holds eventually; no false identity at `N = 0` is needed. -/
theorem normalizedSignedSum_eventuallyEq (A : Set ℕ) :
    normalizedSignedSum A =ᶠ[atTop]
      (fun N : ℕ => 2 * A.partialDensity Set.univ N - 1) := by
  filter_upwards [eventually_ge_atTop 1] with N hN
  exact normalizedSignedSum_eq A (by omega)

/-- General density/signed-sum equivalence. This does not assert either limit. -/
theorem hasDensity_iff_tendsto_signedSum (A : Set ℕ) (d : ℝ) :
    A.HasDensity d ↔
      Tendsto (normalizedSignedSum A) atTop (𝓝 (2 * d - 1)) := by
  rw [Set.HasDensity]
  constructor
  · intro h
    exact ((h.const_mul 2).sub_const 1).congr'
      (normalizedSignedSum_eventuallyEq A).symm
  · intro h
    have h' := (h.add_const 1).div_const 2
    have hd : (2 * d - 1 + 1) / 2 = d := by ring
    rw [hd] at h'
    apply h'.congr'
    filter_upwards [normalizedSignedSum_eventuallyEq A] with N hN
    rw [hN]
    ring

/-- Density one half is equivalent to cancellation of the full signed prefix sum. -/
theorem hasDensity_half_iff (A : Set ℕ) :
    A.HasDensity (1 / 2) ↔
      Tendsto (fun N : ℕ =>
        ((∑ n ∈ Finset.range N, signedIndicator A n : ℤ) : ℝ) / N)
        atTop (𝓝 0) := by
  change A.HasDensity (1 / 2) ↔
    Tendsto (normalizedSignedSum A) atTop (𝓝 0)
  simpa only [show (2 : ℝ) * (1 / 2) - 1 = 0 by norm_num] using
    hasDensity_iff_tendsto_signedSum A (1 / 2)

end DensityReduction

namespace Erdos371

/-- The exact original ascending-comparison set, without deleting any initial indices. -/
def Asc : Set ℕ := {n : ℕ | Nat.maxPrimeFac (n + 1) > Nat.maxPrimeFac n}

/-- Count ascending comparisons in `range N`, including the comparisons at zero and one. -/
def countAsc (N : ℕ) : ℕ :=
  ((Finset.range N).filter
    (fun n => Nat.maxPrimeFac (n + 1) > Nat.maxPrimeFac n)).card

/-- The total signed sum, as distinct from `comparisonSum`, which starts at two. -/
def totalComparisonSum (N : ℕ) : ℤ :=
  ∑ n ∈ Finset.range N, comparisonSign n

/-- The existing comparison sign is the signed indicator of the exact target set. -/
theorem comparisonSign_eq_signedIndicator (n : ℕ) :
    comparisonSign n = DensityReduction.signedIndicator Asc n := by
  classical
  simp [comparisonSign, DensityReduction.signedIndicator, Asc, gt_iff_lt]

/-- The ascending count is the generic prefix count. -/
theorem countAsc_eq_countBelow (N : ℕ) :
    countAsc N = DensityReduction.countBelow Asc N := by
  classical
  simp only [countAsc, DensityReduction.countBelow, Asc, Set.mem_setOf_eq, gt_iff_lt]

/-- The ascending count is exactly the set cardinality in the original density definition. -/
theorem countAsc_eq_ncard (N : ℕ) :
    countAsc N = (Asc ∩ Set.Iio N).ncard := by
  rw [countAsc_eq_countBelow, DensityReduction.countBelow_eq_ncard]

/-- Both initial comparisons really are ascending under the conventions for `maxPrimeFac`. -/
theorem zero_mem_Asc : 0 ∈ Asc := by
  simp [Asc]

theorem one_mem_Asc : 1 ∈ Asc := by
  simp [Asc, Nat.prime_two.maxPrimeFac_eq_self]

@[simp]
theorem comparisonSign_zero : comparisonSign 0 = 1 := by
  simp [comparisonSign]

@[simp]
theorem comparisonSign_one : comparisonSign 1 = 1 := by
  simp [comparisonSign, Nat.prime_two.maxPrimeFac_eq_self]

/-- The exact total sum is the generic signed-indicator sum. -/
theorem totalComparisonSum_eq_signedSum (N : ℕ) :
    totalComparisonSum N = DensityReduction.signedSum Asc N := by
  simp only [totalComparisonSum, DensityReduction.signedSum,
    comparisonSign_eq_signedIndicator]

/-- Exact total signed sum `= 2 * countAsc - N`, with no exceptional initial terms. -/
theorem totalComparisonSum_eq_two_mul_countAsc_sub (N : ℕ) :
    totalComparisonSum N = 2 * (countAsc N : ℤ) - (N : ℤ) := by
  rw [totalComparisonSum_eq_signedSum,
    DensityReduction.signedSum_eq_two_mul_countBelow_sub, ← countAsc_eq_countBelow]

/-- The same exact identity in terms of the original set's cardinality below `N`. -/
theorem totalComparisonSum_eq_two_mul_ncard_sub (N : ℕ) :
    totalComparisonSum N = 2 * ((Asc ∩ Set.Iio N).ncard : ℤ) - (N : ℤ) := by
  rw [totalComparisonSum_eq_two_mul_countAsc_sub, countAsc_eq_ncard]

/-- Conditional reduction using the named total prefix sum. -/
theorem asc_hasDensity_half_iff_totalComparisonSum :
    Asc.HasDensity (1 / 2) ↔
      Tendsto (fun N : ℕ => (totalComparisonSum N : ℝ) / N) atTop (𝓝 0) := by
  simpa only [totalComparisonSum, ← comparisonSign_eq_signedIndicator] using
    DensityReduction.hasDensity_half_iff Asc

/-- Exact original target, equivalent to cancellation of the `range N` comparison-sign sum.
This is an equivalence only, not a settlement of either side. -/
theorem original_density_iff_signedSum :
    {n : ℕ | Nat.maxPrimeFac (n + 1) > Nat.maxPrimeFac n}.HasDensity (1 / 2) ↔
      Tendsto (fun N : ℕ =>
        ((∑ n ∈ Finset.range N, comparisonSign n : ℤ) : ℝ) / N)
        atTop (𝓝 0) := by
  exact asc_hasDensity_half_iff_totalComparisonSum

/-- Exact omission of the initial indices, with matched upper endpoints.
`comparisonSum` uses an inclusive endpoint, so its endpoint here is `N - 1`. -/
theorem totalComparisonSum_eq_comparisonSum_pred_add (N : ℕ) :
    totalComparisonSum N = comparisonSum (N - 1) + ((min N 2 : ℕ) : ℤ) := by
  by_cases hN : 2 ≤ N
  · have hinterval : Finset.Ico 2 N = Finset.Icc 2 (N - 1) := by
      ext n
      simp only [Finset.mem_Ico, Finset.mem_Icc]
      omega
    have hsplit := Finset.sum_range_add_sum_Ico comparisonSign hN
    rw [hinterval] at hsplit
    simpa [totalComparisonSum, comparisonSum, min_eq_right hN,
      Finset.sum_range_succ, add_comm] using hsplit.symm
  · have hsmall : N < 2 := by omega
    interval_cases N <;>
      simp [totalComparisonSum, comparisonSum]

/-- Deleting exactly the prefix at zero and one changes the matched sum by at most two. -/
theorem abs_totalComparisonSum_sub_comparisonSum_pred_le_two (N : ℕ) :
    |totalComparisonSum N - comparisonSum (N - 1)| ≤ (2 : ℤ) := by
  rw [totalComparisonSum_eq_comparisonSum_pred_add, add_sub_cancel_left,
    abs_of_nonneg (Int.natCast_nonneg _)]
  exact_mod_cast min_le_right N 2

/-- The corresponding normalized limits are equivalent; the prefix error is `2 / N`
eventually, hence tends to zero. -/
theorem totalComparisonSum_tendsto_zero_iff_pred :
    Tendsto (fun N : ℕ => (totalComparisonSum N : ℝ) / N) atTop (𝓝 0) ↔
      Tendsto (fun N : ℕ => (comparisonSum (N - 1) : ℝ) / N) atTop (𝓝 0) := by
  have heq : (fun N : ℕ => (totalComparisonSum N : ℝ) / N) =ᶠ[atTop]
      (fun N : ℕ => (comparisonSum (N - 1) : ℝ) / N + (2 : ℝ) / N) := by
    filter_upwards [eventually_ge_atTop 2] with N hN
    rw [totalComparisonSum_eq_comparisonSum_pred_add, min_eq_right hN]
    push_cast
    rw [add_div]
  have htwo := tendsto_const_div_atTop_nhds_zero_nat (2 : ℝ)
  constructor
  · intro h
    simpa only [add_sub_cancel_right, sub_zero] using (h.congr' heq).sub htwo
  · intro h
    simpa only [add_zero] using (h.add htwo).congr' heq.symm

/-- Adding the next index to the total prefix sum. -/
theorem totalComparisonSum_succ (N : ℕ) :
    totalComparisonSum (N + 1) = totalComparisonSum N + comparisonSign N :=
  Finset.sum_range_succ comparisonSign N

/-- At the same inclusive endpoint, there is also a final boundary term.
This prevents confusing `range N` with the interval ending at `N`. -/
theorem totalComparisonSum_eq_comparisonSum_add_two_sub {N : ℕ} (hN : 1 ≤ N) :
    totalComparisonSum N = comparisonSum N + 2 - comparisonSign N := by
  have h := totalComparisonSum_eq_comparisonSum_pred_add (N + 1)
  rw [Nat.add_sub_cancel, min_eq_right (by omega : 2 ≤ N + 1),
    totalComparisonSum_succ] at h
  omega

/-- The single final boundary sign, divided by `N`, always tends to zero.
This is only boundedness of a sign, not cancellation of a sum of signs. -/
theorem comparisonSign_div_tendsto_zero :
    Tendsto (fun N : ℕ => (comparisonSign N : ℝ) / N) atTop (𝓝 0) := by
  apply tendsto_bdd_div_atTop_nhds_zero (b := (-1 : ℝ)) (B := (1 : ℝ))
  · exact Filter.Eventually.of_forall fun N => by
      rcases comparisonSign_eq_one_or_neg_one N with h | h <;> rw [h] <;> norm_num
  · exact Filter.Eventually.of_forall fun N => by
      rcases comparisonSign_eq_one_or_neg_one N with h | h <;> rw [h] <;> norm_num
  · exact tendsto_natCast_atTop_atTop

/-- The existing inclusive-endpoint `comparisonSum N / N` also has the equivalent
zero-limit condition. The initial prefix and final boundary term both vanish after normalization. -/
theorem totalComparisonSum_tendsto_zero_iff_comparisonSum :
    Tendsto (fun N : ℕ => (totalComparisonSum N : ℝ) / N) atTop (𝓝 0) ↔
      Tendsto (fun N : ℕ => (comparisonSum N : ℝ) / N) atTop (𝓝 0) := by
  let error : ℕ → ℝ := fun N => (2 : ℝ) / N - (comparisonSign N : ℝ) / N
  have herr : Tendsto error atTop (𝓝 0) := by
    simpa only [sub_zero] using
      (tendsto_const_div_atTop_nhds_zero_nat (2 : ℝ)).sub comparisonSign_div_tendsto_zero
  have heq : (fun N : ℕ => (totalComparisonSum N : ℝ) / N) =ᶠ[atTop]
      (fun N : ℕ => (comparisonSum N : ℝ) / N + error N) := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    rw [totalComparisonSum_eq_comparisonSum_add_two_sub hN]
    dsimp only [error]
    push_cast
    ring
  constructor
  · intro h
    simpa only [add_sub_cancel_right, sub_zero] using (h.congr' heq).sub herr
  · intro h
    simpa only [add_zero] using (h.add herr).congr' heq.symm

/-- Conditional version of the exact original target using the preexisting `comparisonSum`. -/
theorem original_density_iff_comparisonSum :
    {n : ℕ | Nat.maxPrimeFac (n + 1) > Nat.maxPrimeFac n}.HasDensity (1 / 2) ↔
      Tendsto (fun N : ℕ => (comparisonSum N : ℝ) / N) atTop (𝓝 0) :=
  asc_hasDensity_half_iff_totalComparisonSum.trans
    totalComparisonSum_tendsto_zero_iff_comparisonSum

end Erdos371

#print axioms DensityReduction.countBelow_eq_ncard
#print axioms DensityReduction.signedSum_eq_two_mul_countBelow_sub
#print axioms DensityReduction.sum_signedIndicator_eq_two_mul_ncard_sub
#print axioms DensityReduction.hasDensity_iff_tendsto_signedSum
#print axioms DensityReduction.hasDensity_half_iff
#print axioms Erdos371.countAsc_eq_ncard
#print axioms Erdos371.totalComparisonSum_eq_two_mul_countAsc_sub
#print axioms Erdos371.totalComparisonSum_eq_two_mul_ncard_sub
#print axioms Erdos371.original_density_iff_signedSum

#print axioms Erdos371.totalComparisonSum_eq_comparisonSum_pred_add
#print axioms Erdos371.abs_totalComparisonSum_sub_comparisonSum_pred_le_two
#print axioms Erdos371.totalComparisonSum_tendsto_zero_iff_pred
#print axioms Erdos371.comparisonSign_div_tendsto_zero
#print axioms Erdos371.totalComparisonSum_tendsto_zero_iff_comparisonSum
#print axioms Erdos371.original_density_iff_comparisonSum
