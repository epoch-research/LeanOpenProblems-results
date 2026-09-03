import Submission.StrictLinearLowerTailCriterion

/-!
Finite counterexamples to two weakenings of the local criterion. These are
not counterexamples to the conjecture in `Spec.lean`.
-/

namespace StrictLinearLowerTailExamples

def adjacentTail : ℕ → ℤ
  | 10 => -1
  | 11 => -12
  | _ => 0

/-- The gap-one exception satisfies even the strict lower bound and the
local size inequality, with upper bound zero. -/
theorem adjacent_unit_exception :
    1 * 0 + 10 * 1 + 2 * 1 ^ 2 + 1 < (10 : ℕ) ^ 2 ∧
    (∀ i ≤ 1, -2 * ((10 + i : ℕ) : ℤ) < adjacentTail (10 + i) ∧
      adjacentTail (10 + i) ≤ 0) ∧
    adjacentTail 10 = 10 * adjacentTail 9 - 1 ∧
    adjacentTail 11 = 11 * adjacentTail 10 - 1 ∧
    (∀ i < 1, ((10 + i : ℕ) : ℤ) ∣ adjacentTail (10 + i + 1) -
      adjacentTail (10 + i) + 1) := by
  refine ⟨by norm_num, ?_, by norm_num [adjacentTail], by norm_num [adjacentTail], ?_⟩
  · intro i hi
    interval_cases i <;> norm_num [adjacentTail]
  · intro i hi
    interval_cases i
    norm_num [adjacentTail]

def boundaryTail : ℕ → ℤ
  | 9 => -1
  | 10 => -11
  | 11 => -22
  | 12 => -12
  | 13 => -1
  | 14 => -15
  | _ => 0

/-- The strict lower bound cannot be replaced by a non-strict one in the
local theorem: a four-step return can touch the value `-2n`. -/
theorem non_strict_lower_exception :
    4 * 0 + 10 * 4 + 2 * 4 ^ 2 + 4 < (10 : ℕ) ^ 2 ∧
    (∀ i ≤ 4, -2 * ((10 + i : ℕ) : ℤ) ≤ boundaryTail (10 + i) ∧
      boundaryTail (10 + i) ≤ 0) ∧
    boundaryTail 10 = 10 * boundaryTail 9 - 1 ∧
    boundaryTail 14 = 14 * boundaryTail 13 - 1 ∧
    (∀ i < 4, ((10 + i : ℕ) : ℤ) ∣ boundaryTail (10 + i + 1) -
      boundaryTail (10 + i) + 1) := by
  refine ⟨by norm_num, ?_, by norm_num [boundaryTail], by norm_num [boundaryTail], ?_⟩
  · intro i hi
    interval_cases i <;> norm_num [boundaryTail]
  · intro i hi
    interval_cases i <;> norm_num [boundaryTail]

#print axioms adjacent_unit_exception
#print axioms non_strict_lower_exception

end StrictLinearLowerTailExamples
