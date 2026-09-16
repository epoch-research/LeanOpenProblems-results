import Mathlib
import Submission.Spec

def is_prime (n : ℕ) : Bool := n.isPrime

#eval (List.range 7).map (fun n => (n, is_prime (a n)))
