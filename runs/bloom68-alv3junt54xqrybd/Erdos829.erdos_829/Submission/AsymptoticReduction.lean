import Submission.DivisorBound
import Submission.ConstrainedDivisors

/-!
# Exact asymptotic reduction for sums of two cubes

The representation count and the count of divisors satisfying the exact
square and parity conditions have the same Big-O bounds at infinity.
The square condition is essential; the unconstrained divisor bound does not
supply the polylogarithmic estimate in the problem.
-/

open Asymptotics Filter

namespace Erdos829Aux

/-- A constrained divisor lies in the necessary cube-root window. -/
theorem constrainedDivisor_window {n s : ℕ} (hs : s ∈ constrainedDivisors n) :
    n ≤ s ^ 3 ∧ s ^ 3 ≤ 4 * n := by
  classical
  simp only [constrainedDivisors, Finset.mem_filter] at hs
  rcases hs.2 with ⟨t, ht, _, heq⟩
  have hts : t ≤ s := Nat.le_of_lt_succ (Finset.mem_range.mp ht)
  have ht2 : t ^ 2 ≤ s ^ 2 := Nat.pow_le_pow_left hts 2
  have hlower : s ^ 3 ≤ s * (s ^ 2 + 3 * t ^ 2) := by
    calc
      s ^ 3 = s * s ^ 2 := by ring
      _ ≤ s * (s ^ 2 + 3 * t ^ 2) :=
        Nat.mul_le_mul_left s (Nat.le_add_right _ _)
  have hupper : s * (s ^ 2 + 3 * t ^ 2) ≤ 4 * s ^ 3 := by
    calc
      s * (s ^ 2 + 3 * t ^ 2) ≤ s * (s ^ 2 + 3 * s ^ 2) := by gcongr
      _ = 4 * s ^ 3 := by ring
  constructor
  · omega
  · omega

/-- Every constrained divisor gives at least one ordered representation. -/
theorem constrainedDivisors_card_le_sumRep (n : ℕ) (hn : n ≠ 0) :
    (constrainedDivisors n).card ≤ AdditiveCombinatorics.sumRep cubes n := by
  rw [sumRep_cubes_eq_card_rootPairs, ← unorderedPairs_card_eq_constrainedDivisors_card n hn]
  exact Finset.card_le_card (Finset.filter_subset _ _)

/-- The two exact counts differ by at most a factor of two. -/
theorem sumRep_le_two_mul_constrainedDivisors_card (n : ℕ) (hn : n ≠ 0) :
    AdditiveCombinatorics.sumRep cubes n ≤ 2 * (constrainedDivisors n).card := by
  rw [sumRep_cubes_eq_card_rootPairs]
  exact rootPairs_card_le_two_mul_constrainedDivisors_card n hn

/-- Ordered representations are Big-O of the exact constrained-divisor count. -/
theorem sumRep_isBigO_constrainedDivisors :
    (fun n : ℕ => (AdditiveCombinatorics.sumRep cubes n : ℝ)) =O[atTop]
      (fun n : ℕ => ((constrainedDivisors n).card : ℝ)) := by
  apply IsBigO.of_bound 2
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hn0 : n ≠ 0 := by omega
  simp only [Real.norm_natCast]
  exact_mod_cast sumRep_le_two_mul_constrainedDivisors_card n hn0

/-- The exact constrained-divisor count is Big-O of ordered representations. -/
theorem constrainedDivisors_isBigO_sumRep :
    (fun n : ℕ => ((constrainedDivisors n).card : ℝ)) =O[atTop]
      (fun n : ℕ => (AdditiveCombinatorics.sumRep cubes n : ℝ)) := by
  apply IsBigO.of_bound 1
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hn0 : n ≠ 0 := by omega
  simp only [Real.norm_natCast, one_mul]
  exact_mod_cast constrainedDivisors_card_le_sumRep n hn0

/-- A Big-O upper bound is equivalent for the two exact counting functions. -/
theorem sumRep_isBigO_iff_constrainedDivisors (g : ℕ → ℝ) :
    ((fun n : ℕ => (AdditiveCombinatorics.sumRep cubes n : ℝ)) =O[atTop] g) ↔
      ((fun n : ℕ => ((constrainedDivisors n).card : ℝ)) =O[atTop] g) := by
  constructor
  · exact fun h => constrainedDivisors_isBigO_sumRep.trans h
  · exact fun h => sumRep_isBigO_constrainedDivisors.trans h

/-- The existential polylogarithmic assertion reduces to the exact divisor count. -/
theorem polylogarithmic_bound_iff :
    (∃ C : ℕ, (fun n : ℕ => (AdditiveCombinatorics.sumRep cubes n : ℝ)) =O[atTop]
      (fun n : ℕ => (Real.log n) ^ C)) ↔
    (∃ C : ℕ, (fun n : ℕ => ((constrainedDivisors n).card : ℝ)) =O[atTop]
      (fun n : ℕ => (Real.log n) ^ C)) := by
  exact exists_congr fun C => sumRep_isBigO_iff_constrainedDivisors _

end Erdos829Aux
