import Submission.PrimeReflectionBoundary

/-! Weights that differ from uniform counting by o(N) cannot repair the
positive-density boundary of `primeReflection`. This concerns a proposed
proof method, not the truth of the original density conjecture. -/

namespace Erdos371
open Finset Filter
open scoped Topology

noncomputable def reflectionEscapeMass (N : ℕ) (w : ℕ → ℝ) : ℝ :=
  ∑ n ∈ range N, if N ≤ primeReflection n then w n else 0

noncomputable def reflectionWeightError (N : ℕ) (w : ℕ → ℝ) : ℝ :=
  ∑ n ∈ range N, |w n - 1|

/-- This estimate even permits signed weights. -/
lemma reflectionEscapeMass_lower (N : ℕ) (w : ℕ → ℝ) :
    (((range N).filter (fun n => N ≤ primeReflection n)).card : ℝ) ≤
      reflectionEscapeMass N w + reflectionWeightError N w := by
  have h (n : ℕ) : (if N ≤ primeReflection n then (1 : ℝ) else 0) ≤
      (if N ≤ primeReflection n then w n else 0) + |w n - 1| := by
    by_cases hn : N ≤ primeReflection n
    · simp only [if_pos hn]
      have := neg_le_abs (w n - 1)
      linarith
    · simp only [if_neg hn, zero_add]
      exact abs_nonneg _
  have hs := sum_le_sum (s := range N) (fun n _ => h n)
  simpa only [sum_add_distrib, sum_boole, reflectionEscapeMass,
    reflectionWeightError] using hs

lemma reflectionEscapeMass_ratio_lower (N : ℕ) (w : ℕ → ℝ) :
    (((range N).filter (fun n => N ≤ primeReflection n)).card : ℝ) / N ≤
      reflectionEscapeMass N w / N + reflectionWeightError N w / N := by
  simpa only [add_div] using div_le_div_of_nonneg_right
    (reflectionEscapeMass_lower N w) (Nat.cast_nonneg (α := ℝ) N)

/-- A vanishing L1 reweighting error still leaves a positive proportion of
mass outside the counting interval after reflection. -/
theorem reflectionEscapeMass_eventually_positive (w : ℕ → ℕ → ℝ)
    (hw : Tendsto (fun N => reflectionWeightError N (w N) / N) atTop (nhds 0)) :
    ∀ᶠ N : ℕ in atTop, (1 / 20000 : ℝ) ≤ reflectionEscapeMass N (w N) / N := by
  have he := hw.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 20000)
  filter_upwards [primeReflection_boundary_positive_proportion, he] with N hN heN
  have hb := reflectionEscapeMass_ratio_lower N (w N)
  linarith

/-- Thus no asymptotically uniform weights make the escaping mass o(N). -/
theorem no_uniform_weights_with_negligible_reflection_escape :
    ¬ ∃ w : ℕ → ℕ → ℝ,
      Tendsto (fun N => reflectionWeightError N (w N) / N) atTop (nhds 0) ∧
      Tendsto (fun N => reflectionEscapeMass N (w N) / N) atTop (nhds 0) := by
  rintro ⟨w, hw, he⟩
  have hl := reflectionEscapeMass_eventually_positive w hw
  have hu := he.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 20000)
  obtain ⟨N, hN, hN'⟩ := (hl.and hu).exists
  exact hN.not_gt hN'

/-- Stationarity for a nonnegative measure supported in `range N` forces
zero weight at every input whose reflected image is outside that range. -/
lemma stationary_reflection_weight_vanishes_on_escape (N : ℕ) (w : ℕ → ℝ)
    (hw : ∀ n < N, 0 ≤ w n)
    (hstat : ∀ m : ℕ, (if m < N then w m else 0) =
      ∑ n ∈ range N, if primeReflection n = m then w n else 0)
    (n : ℕ) (hn : n < N) (he : N ≤ primeReflection n) : w n = 0 := by
  have hzero := hstat (primeReflection n)
  rw [if_neg (by omega : ¬ primeReflection n < N)] at hzero
  have hterm : w n ≤ ∑ k ∈ range N,
      if primeReflection k = primeReflection n then w k else 0 := by
    simpa only [if_true] using single_le_sum
      (s := range N) (f := fun k => if primeReflection k = primeReflection n then w k else 0)
      (fun k hk => by dsimp only; split_ifs; exact hw k (mem_range.mp hk); rfl)
      (mem_range.mpr hn)
  exact le_antisymm (by linarith) (hw n hn)

lemma stationary_reflection_escapeMass_zero (N : ℕ) (w : ℕ → ℝ)
    (hw : ∀ n < N, 0 ≤ w n)
    (hstat : ∀ m : ℕ, (if m < N then w m else 0) =
      ∑ n ∈ range N, if primeReflection n = m then w n else 0) :
    reflectionEscapeMass N w = 0 := by
  apply sum_eq_zero
  intro n hn
  split_ifs with he
  · exact stationary_reflection_weight_vanishes_on_escape N w hw hstat n (mem_range.mp hn) he
  · rfl

/-- Every nonnegative invariant measure supported on the original interval
has a definite L1 distance from uniform counting. No normalization of its
total mass is needed for this conclusion. -/
theorem stationary_reflection_weight_error_lower :
    ∀ᶠ N : ℕ in atTop, ∀ w : ℕ → ℝ,
      (∀ n < N, 0 ≤ w n) →
      (∀ m : ℕ, (if m < N then w m else 0) =
        ∑ n ∈ range N, if primeReflection n = m then w n else 0) →
      (1 / 10000 : ℝ) ≤ reflectionWeightError N w / N := by
  filter_upwards [primeReflection_boundary_positive_proportion] with N hN
  intro w hw hstat
  have hb := reflectionEscapeMass_ratio_lower N w
  rw [stationary_reflection_escapeMass_zero N w hw hstat, zero_div, zero_add] at hb
  exact hN.trans hb

#print axioms no_uniform_weights_with_negligible_reflection_escape
#print axioms stationary_reflection_weight_error_lower
end Erdos371
