import Submission.Arithmetic
import Submission.DensityReduction

/-!
# An unconditional sparse boundary for Erdős 371

The set of integers `n ≥ 2` whose greatest prime factor occurs at least twice
has ordinary natural density zero. For a fixed cutoff `Y`, split this set
into `(Y + 1)`-smooth numbers and positive multiples of `m²` for some `m > Y`.
Mathlib's elementary square-times-squarefree decomposition bounds the first
count by `2 ^ #(Y + 1).primesBelow * Nat.sqrt N`. A finite union bound and a
telescoping reciprocal-square estimate bound the second count by `N / Y`.
First let `N → ∞`, then let `Y → ∞`.

Zero and one are excluded from the boundary definition. The last results
also discard the comparisons with a boundary root on either side. This file
does not prove, assume, or import the conjecture or signed-sum cancellation.
Its only imports are the verified arithmetic and conditional density files.
-/

open Filter
open scoped Topology

namespace Erdos371.SparseBoundary

/-- The repeated-greatest-prime-factor boundary, with both junk endpoints removed. -/
def repeatedMax : Set ℕ := {n : ℕ | 2 ≤ n ∧ Nat.maxPrimeFac n ^ 2 ∣ n}

/-- A positive number divisible by the square of an integer above the cutoff.
The integer need not be prime; this deliberately enlarges the rough part. -/
def largeSquareMultiples (Y : ℕ) : Set ℕ :=
  {n : ℕ | n ≠ 0 ∧ ∃ m : ℕ, Y < m ∧ m ^ 2 ∣ n}

/-- A comparison whose left or right actual root has a repeated maximum. -/
def dirtyComparison : Set ℕ :=
  {n : ℕ | 2 ≤ n ∧
    (Nat.maxPrimeFac n ^ 2 ∣ n ∨ Nat.maxPrimeFac (n + 1) ^ 2 ∣ n + 1)}

/-- Prefix counting is monotone under set inclusion. -/
theorem countBelow_mono {A B : Set ℕ} (h : A ⊆ B) (N : ℕ) :
    DensityReduction.countBelow A N ≤ DensityReduction.countBelow B N := by
  classical
  unfold DensityReduction.countBelow
  apply Finset.card_le_card
  intro n hn
  simp only [Finset.mem_filter] at hn ⊢
  exact ⟨hn.1, h hn.2⟩

/-- The elementary finite union bound, with exactly the same prefix on both sides. -/
theorem countBelow_union_le (A B : Set ℕ) (N : ℕ) :
    DensityReduction.countBelow (A ∪ B) N ≤
      DensityReduction.countBelow A N + DensityReduction.countBelow B N := by
  classical
  unfold DensityReduction.countBelow
  simp only [Set.mem_union]
  rw [Finset.filter_or]
  exact Finset.card_union_le _ _

/-- The library smooth-number estimate applies to the strict prefix `range N`. -/
theorem smoothNumbers_count_le (Y N : ℕ) :
    DensityReduction.countBelow (Nat.smoothNumbers Y) N ≤
      2 ^ Y.primesBelow.card * N.sqrt := by
  classical
  calc
    DensityReduction.countBelow (Nat.smoothNumbers Y) N ≤
        (Nat.smoothNumbersUpTo N Y).card := by
      unfold DensityReduction.countBelow
      apply Finset.card_le_card
      intro n hn
      simp only [Finset.mem_filter, Finset.mem_range] at hn
      exact Nat.mem_smoothNumbersUpTo.mpr ⟨hn.1.le, hn.2⟩
    _ ≤ 2 ^ Y.primesBelow.card * N.sqrt := Nat.smoothNumbersUpTo_card_le N Y

/-- The natural square root, divided by the original natural cutoff, tends to zero. -/
theorem natSqrt_div_tendsto_zero :
    Tendsto (fun N : ℕ => (N.sqrt : ℝ) / N) atTop (𝓝 0) := by
  have hreal : Tendsto (fun N : ℕ => Real.sqrt N / N) atTop (𝓝 0) := by
    simpa only [Real.sqrt_div_self] using
      tendsto_inv_atTop_zero.comp
        (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  apply squeeze_zero (fun N => by positivity) (fun N => ?_) hreal
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
  apply (Real.le_sqrt (Nat.cast_nonneg _) (Nat.cast_nonneg _)).mpr
  exact_mod_cast Nat.sqrt_le' N

/-- Complete fixed-cutoff smooth-number result in normalized-cardinality form. -/
theorem smoothNumbers_normalized_tendsto_zero (Y : ℕ) :
    Tendsto (fun N : ℕ =>
      (DensityReduction.countBelow (Nat.smoothNumbers Y) N : ℝ) / N)
      atTop (𝓝 0) := by
  apply squeeze_zero (fun N => by positivity)
    (fun N => div_le_div_of_nonneg_right
      (Nat.cast_le.mpr (smoothNumbers_count_le Y N)) (Nat.cast_nonneg N))
  simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, mul_div_assoc, mul_zero] using
    natSqrt_div_tendsto_zero.const_mul (2 ^ Y.primesBelow.card : ℝ)

/-- For every fixed finite prime cutoff, smooth numbers have ordinary density zero. -/
theorem smoothNumbers_hasDensity_zero (Y : ℕ) :
    (Nat.smoothNumbers Y).HasDensity 0 := by
  simpa only [Set.HasDensity, DensityReduction.partialDensity_eq_countBelow_div] using
    smoothNumbers_normalized_tendsto_zero Y

/-- A positive integer with bounded greatest prime factor is library-smooth. -/
theorem mem_smoothNumbers_of_maxPrimeFac_le {n Y : ℕ}
    (hn : n ≠ 0) (hY : Nat.maxPrimeFac n ≤ Y) :
    n ∈ Nat.smoothNumbers (Y + 1) := by
  apply Nat.mem_smoothNumbers'.mpr
  intro p hp hd
  exact Nat.lt_succ_of_le ((Nat.le_maxPrimeFac hn hp hd).trans hY)

/-- In particular the fixed-`Y` bounded-maximum set, with endpoints excluded, has density zero. -/
theorem boundedMax_hasDensity_zero (Y : ℕ) :
    {n : ℕ | 2 ≤ n ∧ Nat.maxPrimeFac n ≤ Y}.HasDensity 0 := by
  have hsub : {n : ℕ | 2 ≤ n ∧ Nat.maxPrimeFac n ≤ Y} ⊆
      Nat.smoothNumbers (Y + 1) := by
    intro n hn
    exact mem_smoothNumbers_of_maxPrimeFac_le (by have := hn.1; omega) hn.2
  simp only [Set.HasDensity, DensityReduction.partialDensity_eq_countBelow_div]
  apply squeeze_zero (fun N => by positivity)
    (fun N => div_le_div_of_nonneg_right
      (Nat.cast_le.mpr (countBelow_mono hsub N)) (Nat.cast_nonneg N))
    (smoothNumbers_normalized_tendsto_zero (Y + 1))

/-- Explicit finite union bound for positive large-square multiples.
No hypothesis on `Y` or `N` is needed, and zero is never counted. -/
theorem largeSquareMultiples_count_le_sum (Y N : ℕ) :
    DensityReduction.countBelow (largeSquareMultiples Y) N ≤
      ∑ m ∈ Finset.Ioc Y N, N / m ^ 2 := by
  classical
  let U : Finset ℕ := (Finset.Ioc Y N).biUnion fun m =>
    (Finset.range (N + 1)).filter (fun n => n ≠ 0 ∧ m ^ 2 ∣ n)
  calc
    DensityReduction.countBelow (largeSquareMultiples Y) N ≤ U.card := by
      unfold DensityReduction.countBelow
      apply Finset.card_le_card
      intro n hn
      simp only [Finset.mem_filter, Finset.mem_range] at hn
      obtain ⟨hn0, m, hmY, hmn⟩ := hn.2
      have hm1 : 1 ≤ m := by omega
      have hmsq : m ≤ m ^ 2 := by nlinarith
      have hmN : m ≤ N :=
        (hmsq.trans (Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hmn)).trans hn.1.le
      apply Finset.mem_biUnion.mpr
      refine ⟨m, Finset.mem_Ioc.mpr ⟨hmY, hmN⟩, ?_⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hn0, hmn⟩
    _ ≤ ∑ m ∈ Finset.Ioc Y N,
        ((Finset.range (N + 1)).filter (fun n => n ≠ 0 ∧ m ^ 2 ∣ n)).card :=
      Finset.card_biUnion_le
    _ = ∑ m ∈ Finset.Ioc Y N, N / m ^ 2 := by
      apply Finset.sum_congr rfl
      intro m _
      exact Nat.card_multiples' N (m ^ 2)

/-- The elementary reciprocal-square tail, uniformly for every finite endpoint. -/
theorem sum_Ioc_reciprocal_sq_le {Y : ℕ} (hY : 0 < Y) (N : ℕ) :
    (∑ m ∈ Finset.Ioc Y N, ((m : ℝ) ^ 2)⁻¹) ≤ (Y : ℝ)⁻¹ := by
  by_cases hYN : Y ≤ N
  · exact (sum_Ioc_inv_sq_le_sub (Nat.ne_of_gt hY) hYN).trans
      (sub_le_self _ (inv_nonneg.mpr (Nat.cast_nonneg N)))
  · have hempty : Finset.Ioc Y N = ∅ := Finset.Ioc_eq_empty_of_le (by omega)
    simp only [hempty, Finset.sum_empty]
    positivity

/-- The rough count is at most `N / Y`, with division in the reals.
The positivity hypothesis on the cutoff is essential for this estimate. -/
theorem largeSquareMultiples_count_le {Y : ℕ} (hY : 0 < Y) (N : ℕ) :
    (DensityReduction.countBelow (largeSquareMultiples Y) N : ℝ) ≤ (N : ℝ) / Y := by
  classical
  calc
    (DensityReduction.countBelow (largeSquareMultiples Y) N : ℝ) ≤
        ((∑ m ∈ Finset.Ioc Y N, N / m ^ 2 : ℕ) : ℝ) :=
      Nat.cast_le.mpr (largeSquareMultiples_count_le_sum Y N)
    _ = ∑ m ∈ Finset.Ioc Y N, ((N / m ^ 2 : ℕ) : ℝ) := by simp only [Nat.cast_sum]
    _ ≤ ∑ m ∈ Finset.Ioc Y N, (N : ℝ) / (m : ℝ) ^ 2 := by
      apply Finset.sum_le_sum
      intro m _
      simpa only [Nat.cast_pow] using (Nat.cast_div_le (m := N) (n := m ^ 2) :
        ((N / m ^ 2 : ℕ) : ℝ) ≤ (N : ℝ) / (m ^ 2 : ℕ))
    _ = (N : ℝ) * (∑ m ∈ Finset.Ioc Y N, ((m : ℝ) ^ 2)⁻¹) := by
      simp only [div_eq_mul_inv, Finset.mul_sum]
    _ ≤ (N : ℝ) * (Y : ℝ)⁻¹ :=
      mul_le_mul_of_nonneg_left (sum_Ioc_reciprocal_sq_le hY N) (Nat.cast_nonneg N)
    _ = (N : ℝ) / Y := rfl

/-- The normalized rough count is uniformly bounded by `1 / Y`.
Both the cutoff and the normalization endpoint are explicitly positive. -/
theorem largeSquareMultiples_normalized_le {Y N : ℕ} (hY : 0 < Y) (hN : 0 < N) :
    (DensityReduction.countBelow (largeSquareMultiples Y) N : ℝ) / N ≤ (1 : ℝ) / Y := by
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)
  calc
    (DensityReduction.countBelow (largeSquareMultiples Y) N : ℝ) / N ≤
        ((N : ℝ) / Y) / N :=
      div_le_div_of_nonneg_right (largeSquareMultiples_count_le hY N) (Nat.cast_nonneg N)
    _ = (1 : ℝ) / Y := by field_simp

/-- The fixed-cutoff split; in the rough part use the actual greatest prime factor. -/
theorem repeatedMax_subset (Y : ℕ) :
    repeatedMax ⊆ Nat.smoothNumbers (Y + 1) ∪ largeSquareMultiples Y := by
  intro n hn
  by_cases h : Nat.maxPrimeFac n ≤ Y
  · exact Or.inl (mem_smoothNumbers_of_maxPrimeFac_le (by have := hn.1; omega) h)
  · exact Or.inr ⟨by have := hn.1; omega, Nat.maxPrimeFac n, by omega, hn.2⟩

/-- Fully explicit finite counting inequality for the boundary.
It is valid even for `Y = 0`, `N = 0`, and `N = 1`. -/
theorem repeatedMax_count_le (Y N : ℕ) :
    DensityReduction.countBelow repeatedMax N ≤
      2 ^ (Y + 1).primesBelow.card * N.sqrt + ∑ m ∈ Finset.Ioc Y N, N / m ^ 2 := by
  calc
    DensityReduction.countBelow repeatedMax N ≤
        DensityReduction.countBelow (Nat.smoothNumbers (Y + 1)) N +
          DensityReduction.countBelow (largeSquareMultiples Y) N :=
      (countBelow_mono (repeatedMax_subset Y) N).trans (countBelow_union_le _ _ _)
    _ ≤ _ := Nat.add_le_add (smoothNumbers_count_le (Y + 1) N)
      (largeSquareMultiples_count_le_sum Y N)

/-- The smooth plus rough estimate at a positive normalization endpoint. -/
theorem repeatedMax_normalized_le {Y N : ℕ} (hY : 0 < Y) (hN : 0 < N) :
    (DensityReduction.countBelow repeatedMax N : ℝ) / N ≤
      (DensityReduction.countBelow (Nat.smoothNumbers (Y + 1)) N : ℝ) / N +
        (1 : ℝ) / Y := by
  have hcount : DensityReduction.countBelow repeatedMax N ≤
      DensityReduction.countBelow (Nat.smoothNumbers (Y + 1)) N +
        DensityReduction.countBelow (largeSquareMultiples Y) N :=
    (countBelow_mono (repeatedMax_subset Y) N).trans (countBelow_union_le _ _ _)
  calc
    (DensityReduction.countBelow repeatedMax N : ℝ) / N ≤
        ((DensityReduction.countBelow (Nat.smoothNumbers (Y + 1)) N : ℝ) +
          (DensityReduction.countBelow (largeSquareMultiples Y) N : ℝ)) / N :=
      div_le_div_of_nonneg_right (by exact_mod_cast hcount) (Nat.cast_nonneg N)
    _ = (DensityReduction.countBelow (Nat.smoothNumbers (Y + 1)) N : ℝ) / N +
        (DensityReduction.countBelow (largeSquareMultiples Y) N : ℝ) / N := add_div _ _ _
    _ ≤ _ := add_le_add le_rfl (largeSquareMultiples_normalized_le hY hN)

/-- Unconditional ordinary normalized-cardinality limit for repeated maxima. -/
theorem repeatedMax_normalized_tendsto_zero :
    Tendsto (fun N : ℕ => (DensityReduction.countBelow repeatedMax N : ℝ) / N)
      atTop (𝓝 0) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    exact Filter.Eventually.of_forall fun N => ha.trans_le (by positivity)
  · intro ε hε
    have hsmall : ∀ᶠ Y : ℕ in atTop, (1 : ℝ) / Y < ε / 2 :=
      (tendsto_order.1
        (tendsto_one_div_atTop_nhds_zero_nat :
          Tendsto (fun Y : ℕ => (1 : ℝ) / Y) atTop (𝓝 0))).2 _ (by linarith)
    obtain ⟨Y, hY, hYs⟩ := ((eventually_ge_atTop 1).and hsmall).exists
    filter_upwards [(tendsto_order.1 (smoothNumbers_normalized_tendsto_zero (Y + 1))).2
      (ε / 2) (by linarith), eventually_ge_atTop 1] with N hNs hN
    exact (repeatedMax_normalized_le (by omega : 0 < Y) (by omega : 0 < N)).trans_lt
      (by linarith)

/-- Genuine unconditional boundary lemma, not the Erdős 371 conjecture. -/
theorem repeatedMax_hasDensity_zero :
    {n : ℕ | 2 ≤ n ∧ Nat.maxPrimeFac n ^ 2 ∣ n}.HasDensity 0 := by
  change repeatedMax.HasDensity 0
  simpa only [Set.HasDensity, DensityReduction.partialDensity_eq_countBelow_div] using
    repeatedMax_normalized_tendsto_zero

/-- The exact set-cardinality formulation used by ordinary natural density. -/
theorem repeatedMax_ncard_tendsto_zero :
    Tendsto (fun N : ℕ =>
      (({n : ℕ | 2 ≤ n ∧ Nat.maxPrimeFac n ^ 2 ∣ n} ∩ Set.Iio N).ncard : ℝ) / N)
      atTop (𝓝 0) := by
  simpa only [DensityReduction.countBelow_eq_ncard, repeatedMax] using
    repeatedMax_normalized_tendsto_zero

/-- Shifting the test by one increases the counting endpoint by exactly one. -/
theorem countBelow_shift_le (A : Set ℕ) (N : ℕ) :
    DensityReduction.countBelow {n : ℕ | n + 1 ∈ A} N ≤
      DensityReduction.countBelow A (N + 1) := by
  classical
  let s := (Finset.range N).filter (fun n => n + 1 ∈ A)
  let t := (Finset.range (N + 1)).filter (fun n => n ∈ A)
  have hsub : s.image (fun n => n + 1) ⊆ t := by
    intro m hm
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hm
    simp only [s, Finset.mem_filter, Finset.mem_range] at hn
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hn.2⟩
  change s.card ≤ t.card
  calc
    s.card = (s.image (fun n => n + 1)).card :=
      (Finset.card_image_of_injective s
        (by intro a b h; change a + 1 = b + 1 at h; omega)).symm
    _ ≤ t.card := Finset.card_le_card hsub

/-- A zero-limit prefix count remains zero when the count endpoint is shifted,
while the denominator remains the original `N`. -/
theorem shifted_count_normalized_tendsto_zero (A : Set ℕ)
    (hA : Tendsto (fun N : ℕ => (DensityReduction.countBelow A N : ℝ) / N)
      atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => (DensityReduction.countBelow A (N + 1) : ℝ) / N)
      atTop (𝓝 0) := by
  have h := (hA.comp (tendsto_add_atTop_nat 1)).mul
    ((tendsto_const_nhds :
        Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 (1 : ℝ))).add
      (tendsto_one_div_atTop_nhds_zero_nat :
        Tendsto (fun N : ℕ => (1 : ℝ) / N) atTop (𝓝 0)))
  simp only [zero_mul] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hN1 : ((N + 1 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  dsimp only [Function.comp_def]
  push_cast at hN1 ⊢
  field_simp

/-- Visible count bound for comparisons with a repeated maximum on either root. -/
theorem dirtyComparison_count_le (N : ℕ) :
    DensityReduction.countBelow dirtyComparison N ≤
      DensityReduction.countBelow repeatedMax N +
        DensityReduction.countBelow repeatedMax (N + 1) := by
  have hsub : dirtyComparison ⊆ repeatedMax ∪ {n : ℕ | n + 1 ∈ repeatedMax} := by
    intro n hn
    rcases hn.2 with h | h
    · exact Or.inl ⟨hn.1, h⟩
    · exact Or.inr ⟨by have := hn.1; omega, h⟩
  exact ((countBelow_mono hsub N).trans (countBelow_union_le _ _ _)).trans
    (Nat.add_le_add le_rfl (countBelow_shift_le repeatedMax N))

/-- The dirty-comparison count also has an unconditional ordinary zero limit. -/
theorem dirtyComparison_normalized_tendsto_zero :
    Tendsto (fun N : ℕ => (DensityReduction.countBelow dirtyComparison N : ℝ) / N)
      atTop (𝓝 0) := by
  apply squeeze_zero (fun N => by positivity)
    (fun N => div_le_div_of_nonneg_right
      (Nat.cast_le.mpr (dirtyComparison_count_le N)) (Nat.cast_nonneg N))
  simpa only [Nat.cast_add, add_div, add_zero] using
    repeatedMax_normalized_tendsto_zero.add
      (shifted_count_normalized_tendsto_zero repeatedMax repeatedMax_normalized_tendsto_zero)

/-- Discarding dirty comparisons costs a set of ordinary natural density zero.
This is only a sparse-boundary statement, not signed-sum cancellation. -/
theorem dirtyComparison_hasDensity_zero :
    {n : ℕ | 2 ≤ n ∧
      (Nat.maxPrimeFac n ^ 2 ∣ n ∨ Nat.maxPrimeFac (n + 1) ^ 2 ∣ n + 1)}.HasDensity 0 := by
  change dirtyComparison.HasDensity 0
  simpa only [Set.HasDensity, DensityReduction.partialDensity_eq_countBelow_div] using
    dirtyComparison_normalized_tendsto_zero

end Erdos371.SparseBoundary

#print axioms Erdos371.SparseBoundary.repeatedMax
#print axioms Erdos371.SparseBoundary.largeSquareMultiples
#print axioms Erdos371.SparseBoundary.dirtyComparison
#print axioms Erdos371.SparseBoundary.countBelow_mono
#print axioms Erdos371.SparseBoundary.countBelow_union_le
#print axioms Erdos371.SparseBoundary.smoothNumbers_count_le
#print axioms Erdos371.SparseBoundary.natSqrt_div_tendsto_zero
#print axioms Erdos371.SparseBoundary.smoothNumbers_normalized_tendsto_zero
#print axioms Erdos371.SparseBoundary.smoothNumbers_hasDensity_zero
#print axioms Erdos371.SparseBoundary.mem_smoothNumbers_of_maxPrimeFac_le
#print axioms Erdos371.SparseBoundary.boundedMax_hasDensity_zero
#print axioms Erdos371.SparseBoundary.largeSquareMultiples_count_le_sum
#print axioms Erdos371.SparseBoundary.sum_Ioc_reciprocal_sq_le
#print axioms Erdos371.SparseBoundary.largeSquareMultiples_count_le
#print axioms Erdos371.SparseBoundary.largeSquareMultiples_normalized_le
#print axioms Erdos371.SparseBoundary.repeatedMax_subset
#print axioms Erdos371.SparseBoundary.repeatedMax_count_le
#print axioms Erdos371.SparseBoundary.repeatedMax_normalized_le
#print axioms Erdos371.SparseBoundary.repeatedMax_normalized_tendsto_zero
#print axioms Erdos371.SparseBoundary.repeatedMax_hasDensity_zero
#print axioms Erdos371.SparseBoundary.repeatedMax_ncard_tendsto_zero
#print axioms Erdos371.SparseBoundary.countBelow_shift_le
#print axioms Erdos371.SparseBoundary.shifted_count_normalized_tendsto_zero
#print axioms Erdos371.SparseBoundary.dirtyComparison_count_le
#print axioms Erdos371.SparseBoundary.dirtyComparison_normalized_tendsto_zero
#print axioms Erdos371.SparseBoundary.dirtyComparison_hasDensity_zero
