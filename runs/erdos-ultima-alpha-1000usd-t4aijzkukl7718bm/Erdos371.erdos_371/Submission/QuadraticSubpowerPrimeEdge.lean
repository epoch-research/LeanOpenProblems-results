import Submission.SmallPrimePairTailMean
import Submission.QuadraticDampingMean

/-! Removing the complete subpower-prime edge from the actual quadratic
signed remainder, with the same cutoff and sampling endpoints. -/
namespace Erdos371
open Finset Filter
open scoped Topology
set_option autoImplicit false

lemma smallCrossPrimePairs_zero (D X : ℕ) : smallCrossPrimePairs D X 0=∅ := by
  simp [smallCrossPrimePairs,largeCrossPrimePairs]

lemma smallCrossPrimePairs_shifted_subpower_mean_zero (X : ℕ → ℕ)
    (hX : ∀ᶠ N : ℕ in atTop, 1 ≤ X N)
    (hlim : Tendsto (fun N : ℕ => Real.log (X N+1 : ℝ)/Real.log N) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ =>
      (∑ n ∈ range N, ((smallCrossPrimePairs (N+1) (X (N+1)) (n+1)).card : ℝ))/N)
      atTop (𝓝 0) := by
  have ht := (smallCrossPrimePairs_subpower_mean_zero X hX hlim).comp (tendsto_add_atTop_nat 1)
  have hr : Tendsto (fun N : ℕ => ((N : ℝ)+1)/N) atTop (𝓝 1) := by
    have hh := tendsto_one_div_atTop_nhds_zero_nat.const_add (1 : ℝ)
    simp only [add_zero] at hh
    apply hh.congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
    have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    field_simp
  have hh := ht.mul hr
  simp only [zero_mul,Function.comp_def] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
  rw [sum_range_succ',smallCrossPrimePairs_zero,card_empty,Nat.cast_zero,add_zero]
  simp only [Nat.cast_add,Nat.cast_one]
  have hn : (N : ℝ)+1 ≠ 0 := by positivity
  field_simp

/-- Absolute negligibility permits arbitrary bounded attached weights,
even weights depending on the cutoff. No independence is required. -/
theorem smallCrossPrimePairs_shifted_weighted_mean_zero (X : ℕ → ℕ)
    (hX : ∀ᶠ N : ℕ in atTop, 1 ≤ X N)
    (hlim : Tendsto (fun N : ℕ => Real.log (X N+1 : ℝ)/Real.log N) atTop (𝓝 0))
    (w : ℕ → ℕ → ℝ) (hw : ∀ N n, |w N n| ≤ 1) :
    Tendsto (fun N : ℕ =>
      (∑ n ∈ range N, (smallCrossPrimePairs (N+1) (X (N+1)) (n+1)).card*w N n)/N)
      atTop (𝓝 0) := by
  apply squeeze_zero_norm _ (smallCrossPrimePairs_shifted_subpower_mean_zero X hX hlim)
  intro N
  rw [norm_div,Real.norm_natCast,Real.norm_eq_abs]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
  apply (abs_sum_le_sum_abs _ _).trans
  apply sum_le_sum
  intro n hn
  rw [abs_mul,abs_of_nonneg (Nat.cast_nonneg _)]
  exact mul_le_of_le_one_right (Nat.cast_nonneg _) (hw N n)

def highMinCrossPrimePairs (D X n : ℕ) : Finset (ℕ×ℕ) :=
  (largeCrossPrimePairs D n).filter fun pq => X < min pq.1 pq.2

lemma largeCrossPrimePairs_card_partition (D X n : ℕ) :
    (largeCrossPrimePairs D n).card =
      (smallCrossPrimePairs D X n).card+(highMinCrossPrimePairs D X n).card := by
  have he := card_filter_add_card_filter_not (s := largeCrossPrimePairs D n)
    (fun pq => min pq.1 pq.2 ≤ X)
  simpa only [not_le,smallCrossPrimePairs,highMinCrossPrimePairs] using he.symm

lemma highMinCrossPrimePairs_point_error (D X n : ℕ) :
    (largeCrossPrimePairs D n).card*factorSign n-(highMinCrossPrimePairs D X n).card*factorSign n =
      (smallCrossPrimePairs D X n).card*factorSign n := by
  rw [largeCrossPrimePairs_card_partition D X n,Nat.cast_add]
  ring

theorem highMinCrossPrimePairs_mean_error_zero (X : ℕ → ℕ)
    (hX : ∀ᶠ N : ℕ in atTop, 1 ≤ X N)
    (hlim : Tendsto (fun N : ℕ => Real.log (X N+1 : ℝ)/Real.log N) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ =>
      (∑ n ∈ range N, (largeCrossPrimePairs (N+1) (n+1)).card*factorSign (n+1))/N-
      (∑ n ∈ range N, (highMinCrossPrimePairs (N+1) (X (N+1)) (n+1)).card*factorSign (n+1))/N)
      atTop (𝓝 0) := by
  have ht := smallCrossPrimePairs_shifted_weighted_mean_zero X hX hlim
    (fun _ n => factorSign (n+1)) (by
      intro N n
      simp only [factorSign,predicateSign]
      split_ifs <;> norm_num)
  convert ht using 1
  ext N
  rw [← sub_div,← sum_sub_distrib]
  simp only [highMinCrossPrimePairs_point_error]

/-- The same quadratic mean is obtained after removing ALL large-product
pairs with a prime below any prescribed subpower cutoff. Signed cancellation
of the retained positive-power prime range is still not asserted. -/
theorem quadraticFactorSign_mean_highMin_error (X : ℕ → ℕ)
    (hX : ∀ᶠ N : ℕ in atTop, 1 ≤ X N)
    (hlim : Tendsto (fun N : ℕ => Real.log (X N+1 : ℝ)/Real.log N) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ =>
      (∑ n ∈ range N, quadraticFactorSign (n+1))/N-
      (∑ n ∈ range N, (highMinCrossPrimePairs (N+1) (X (N+1)) (n+1)).card*factorSign (n+1))/N)
      atTop (𝓝 0) := by
  have ht := quadraticFactorSign_mean_large_pair_error.add (highMinCrossPrimePairs_mean_error_zero X hX hlim)
  simp only [add_zero] at ht
  convert ht using 1
  ext N
  ring

#print axioms smallCrossPrimePairs_shifted_weighted_mean_zero
#print axioms quadraticFactorSign_mean_highMin_error
end Erdos371
