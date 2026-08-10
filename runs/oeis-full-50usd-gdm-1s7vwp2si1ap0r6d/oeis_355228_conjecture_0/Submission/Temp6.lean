import FormalConjectures.Util.ProblemImports
set_option maxRecDepth 1000000
open Finset Nat Set

def can_sum (k : ℕ) (target : ℕ) : List ℕ → Bool
  | [] => k == 0 && target == 0
  | x :: xs =>
    (x ≤ target && k > 0 && can_sum (k - 1) (target - x) xs) || can_sum k target xs

-- Let us check if this runs and evaluates to false for 120, 144, 168.
#eval can_sum 13 120 [1, 2, 3, 4, 5, 6, 8, 10, 12, 15, 20, 24, 30, 40, 60, 120]
#eval can_sum 13 144 [1, 2, 3, 4, 6, 8, 9, 12, 16, 18, 24, 36, 48, 72, 144]
#eval can_sum 13 168 [1, 2, 3, 4, 6, 7, 8, 12, 14, 21, 24, 28, 42, 56, 84, 168]

lemma test_120 : can_sum 13 120 [1, 2, 3, 4, 5, 6, 8, 10, 12, 15, 20, 24, 30, 40, 60, 120] = false := by rfl
lemma test_144 : can_sum 13 144 [1, 2, 3, 4, 6, 8, 9, 12, 16, 18, 24, 36, 48, 72, 144] = false := by rfl
lemma test_168 : can_sum 13 168 [1, 2, 3, 4, 6, 7, 8, 12, 14, 21, 24, 28, 42, 56, 84, 168] = false := by rfl
