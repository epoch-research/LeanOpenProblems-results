import Submission.Spec
open Nat List Finset

def get_divisors (n : ℕ) : List ℕ :=
  (List.range (n + 1)).filter (fun d => d > 0 ∧ n % d = 0)

theorem div_eq (n : ℕ) : (Nat.divisors n).sort (· ≤ ·) = get_divisors n := by
  sorry
