import Submission.Identity
import Mathlib

open Nat

lemma descFactorial_mul_factorial (A B : ℕ) (h : B ≤ A) :
    A.descFactorial B * (A - B).factorial = A.factorial := by
  have := Nat.factorial_mul_descFactorial h
  rw [mul_comm] at this
  exact this

lemma poly_id_Z (n r : ℕ) (hr : r ≤ 4 * n) :
    D n r * (2 ^ r : ℤ) * ((4 * n).factorial : ℤ) * ((8 * n - 2 * r).factorial : ℤ) =
    ((8 * n).factorial : ℤ) * ((4 * n - r).factorial : ℤ) := by
  have e1 := identity_Z n r hr
  -- multiply e1 by (4n-r)! * (8n-2r)!
  have h4 : ((4 * n).descFactorial r : ℤ) * ((4 * n - r).factorial : ℤ) = ((4 * n).factorial : ℤ) := by
    have := descFactorial_mul_factorial (4 * n) r hr
    exact_mod_cast this
  have hr2 : 2 * r ≤ 8 * n := by omega
  have h8 : ((8 * n).descFactorial (2 * r) : ℤ) * ((8 * n - 2 * r).factorial : ℤ) = ((8 * n).factorial : ℤ) := by
    have := descFactorial_mul_factorial (8 * n) (2 * r) hr2
    exact_mod_cast this

  calc D n r * (2 ^ r : ℤ) * ↑((4 * n).factorial) * ↑((8 * n - 2 * r).factorial)
    = D n r * (2 ^ r : ℤ) * (↑((4 * n).descFactorial r) * ↑((4 * n - r).factorial)) * ↑((8 * n - 2 * r).factorial) := by rw [h4]
  _ = (D n r * (2 ^ r : ℤ) * ↑((4 * n).descFactorial r)) * ↑((4 * n - r).factorial) * ↑((8 * n - 2 * r).factorial) := by ring
  _ = ↑((8 * n).descFactorial (2 * r)) * ↑((4 * n - r).factorial) * ↑((8 * n - 2 * r).factorial) := by rw [e1]
  _ = (↑((8 * n).descFactorial (2 * r)) * ↑((8 * n - 2 * r).factorial)) * ↑((4 * n - r).factorial) := by ring
  _ = ↑((8 * n).factorial) * ↑((4 * n - r).factorial) := by rw [h8]
