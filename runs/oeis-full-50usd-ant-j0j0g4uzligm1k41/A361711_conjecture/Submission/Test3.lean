import Mathlib
open Finset BigOperators Nat

example (a k : ℕ) :
    ((a+k+2).choose k : ℚ) * ((k ! : ℚ) * ((a+2)! : ℚ)) = ((a+k+2)! : ℚ) := by
  have h := Nat.choose_mul_factorial_mul_factorial (n := a+k+2) (k := k) (by omega)
  have hsub : (a+k+2) - k = a+2 := by omega
  rw [hsub] at h
  have := congrArg (fun x : ℕ => (x : ℚ)) h
  push_cast at this
  linarith [this]

-- factorial expansion
example (a k : ℕ) : ((a+k+2)! : ℚ) = (a+k+2)*(a+k+1)*((a+k)! : ℚ) := by
  have : a+k+2 = (a+k+1)+1 := by omega
  rw [this, Nat.factorial_succ]
  have : a+k+1 = (a+k)+1 := by omega
  rw [this, Nat.factorial_succ]
  push_cast; ring
