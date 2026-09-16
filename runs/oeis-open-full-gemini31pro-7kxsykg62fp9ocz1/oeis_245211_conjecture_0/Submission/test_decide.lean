import Mathlib
import Submission.Spec
def a_comp (n : ℕ) : ℕ := ((n.divisors).sum (fun d => d * d.divisors.card)) - n * n.divisors.card
def check_range (m : ℕ) : Bool := (List.range m).all (fun n => if 0 < n ∧ n ≠ 21 then a_comp n ≠ n else true)
#eval check_range 50000
