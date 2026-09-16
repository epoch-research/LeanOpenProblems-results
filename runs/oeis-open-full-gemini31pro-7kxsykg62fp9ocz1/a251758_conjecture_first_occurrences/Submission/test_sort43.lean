import Submission.test_sort30
import Submission.Spec

def a_comp (n : ℕ) : ℕ :=
  let divs := list_divisors n
  let s := (divs.zip divs.tail).map (fun p => p.1 * p.2) |>.sum
  if s = 0 then 0 else n ^ 2 / s

theorem a_eq_a_comp (n : ℕ) (hn : n ≠ 0) : a n = a_comp n := by
  unfold a a_comp
  have h := list_divisors_eq n hn
  -- We need to replace `(Nat.divisors n).sort (· ≤ ·)` with `list_divisors n`
  -- But they are equal in reverse.
  sorry
