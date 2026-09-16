import Submission.PolyId33
import Mathlib

open Nat

lemma D_times_even_eq_all (X : ℕ) (r : ℕ) (hr : 2 * r ≤ 8 * X) :
  ((List.range r).map (fun (k:ℕ) => 8 * (X:ℤ) - 2 * (k:ℤ) - 1)).prod *
  ((2:ℤ)^r * ((4 * X).descFactorial r : ℤ))
  = ((8 * X).descFactorial (2 * r) : ℤ) := by
  have H1 := odd_even_split (X:ℤ) r
  have H2 := descFactorial_eq_prod_even X r (by omega)
  have H3 := descFactorial_eq_prod_all X (2 * r) hr
  rw [← H2]
  rw [H1]
  rw [H3]
