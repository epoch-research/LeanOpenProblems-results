import Submission.FallingBoundaryBarrier

/-!
The fixed two-node residue family has an irreducible first-column error.
This auxiliary obstruction applies to aggregate-denominator clearing too;
it does not settle Erdős 68 or treat increasing interpolation degree.
-/
namespace FallingAggregateBarrier
open FallingResidueForms FallingBoundaryBarrier Erdos68Development TailPowerExpansion

lemma first_column_gap :
    (1/20:ℝ) < (∑' k : ℕ, powerTerm 0 k) - (2/3:ℝ) := by
  have h := (powerTerm_partial_sum_error 0 4).1
  have hs : (∑ k ∈ Finset.range 4, powerTerm 0 k) = (43/60:ℝ) := by
    norm_num [Finset.sum_range_succ, powerTerm]
  rw [hs] at h
  linarith

/-- The aggregate boundary stays more than 1/20 below the target, for
all truncation lengths. This is independent of denominator cancellation. -/
theorem aggregate_error_lower (r : ℕ) :
    (1/20:ℝ) < (∑' k : ℕ, term k) - (approximation r : ℝ) := by
  have he := finite_tail_expansion (r+1) 0
  simp only [columnTail, Nat.add_zero] at he
  have ht := tailError_pos (r+1) 0
  let gap : ℕ → ℝ := fun j => (∑' k : ℕ, powerTerm j k) -
    (boundary j : ℝ)/(leading j : ℝ)
  have hnonneg (j : ℕ) : 0 ≤ gap j := (sub_pos.mpr (normalized_boundary_lt j)).le
  have hfirst : (1/20:ℝ) < gap 0 := by
    dsimp [gap]
    norm_num [boundary, leading]
    exact first_column_gap
  have hsum : gap 0 ≤ ∑ j ∈ Finset.range (r+1), gap j := by
    exact Finset.single_le_sum (fun j _ => hnonneg j) (by simp)
  have hsum_eq : (∑ j ∈ Finset.range (r+1), gap j) =
      (∑ j ∈ Finset.range (r+1), ∑' k : ℕ, powerTerm j k) -
        (approximation r : ℝ) := by
    simp only [gap, Finset.sum_sub_distrib, approximation, Rat.cast_sum,
      Rat.cast_div, Rat.cast_intCast]
  rw [hsum_eq] at hsum
  linarith

/-- Any positive integer multiplier preserves the fixed positive gap.
In particular this applies to the reduced aggregate denominator itself. -/
theorem scaled_aggregate_error_lower (r : ℕ) (m : ℤ) (hm : 0 < m) :
    (1/20:ℝ) < (m:ℝ)*((∑' k : ℕ, term k) - (approximation r : ℝ)) := by
  have he := aggregate_error_lower r
  have hm1 : (1:ℝ) ≤ m := by exact_mod_cast (show (1:ℤ) ≤ m by omega)
  have hnonneg : 0 ≤ (∑' k : ℕ, term k) - (approximation r : ℝ) := by linarith
  exact he.trans_le (by simpa using mul_le_mul_of_nonneg_right hm1 hnonneg)

theorem reduced_aggregate_error_lower (r : ℕ) :
    (1/20:ℝ) < ((approximation r).den:ℝ)*
      ((∑' k : ℕ, term k) - (approximation r : ℝ)) := by
  exact_mod_cast scaled_aggregate_error_lower r ((approximation r).den : ℤ)
    (by exact_mod_cast (approximation r).pos)

open Filter
open scoped Topology

/-- No choice of truncation subsequence or positive integer multipliers
makes these fixed-family forms tend to zero. -/
theorem not_tendsto_scaled_errors (index : ℕ → ℕ) (m : ℕ → ℤ)
    (hm : ∀ n, 0 < m n) :
    ¬ Tendsto (fun n => (m n : ℝ)*
      ((∑' k : ℕ, term k) - (approximation (index n) : ℝ))) atTop (𝓝 0) := by
  intro h
  have hh : (1/20:ℝ) ≤ 0 := ge_of_tendsto h (Eventually.of_forall
    (fun n => (scaled_aggregate_error_lower (index n) (m n) (hm n)).le))
  norm_num at hh

end FallingAggregateBarrier

#print axioms FallingAggregateBarrier.aggregate_error_lower
#print axioms FallingAggregateBarrier.scaled_aggregate_error_lower
#print axioms FallingAggregateBarrier.reduced_aggregate_error_lower

#print axioms FallingAggregateBarrier.not_tendsto_scaled_errors
