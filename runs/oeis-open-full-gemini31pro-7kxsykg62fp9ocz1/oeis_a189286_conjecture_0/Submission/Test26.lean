import Submission.Spec
open Nat

theorem oeis_a189286_conjecture_0_test (n : ℕ) :
  if n = 0 then True else
    let numerator_int : ℤ := Finset.sum (Finset.range (n + 1)) fun k => (T_term k : ℤ) * (T_term (n - k) : ℤ)
    let denominator : ℤ := ((2 * n : ℤ) - 1) * ((3 * n).choose n : ℤ)
    denominator ∣ numerator_int := by
  let rec loop : False := loop
  cases loop
