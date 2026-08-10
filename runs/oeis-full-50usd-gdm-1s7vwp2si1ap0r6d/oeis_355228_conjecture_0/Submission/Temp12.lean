import FormalConjectures.Util.ProblemImports
set_option maxRecDepth 1000000
open Finset Nat Set

def can_sum (k : ℕ) (target : ℕ) : List ℕ → Bool
  | [] => k == 0 && target == 0
  | x :: xs =>
    (x ≤ target && k > 0 && can_sum (k - 1) (target - x) xs) || can_sum k target xs

lemma test_120 : can_sum 13 120 (Nat.divisors 120).toList = false := by decide
lemma test_144 : can_sum 13 144 (Nat.divisors 144).toList = false := by decide
lemma test_168 : can_sum 13 168 (Nat.divisors 168).toList = false := by decide
