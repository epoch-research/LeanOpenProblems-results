import Submission.Spec
import Mathlib.Tactic

open Int

def fibZ (n : ℕ) : ℤ := (Nat.fib n : ℤ)

-- Wait, I should just use `Spec.lean`
