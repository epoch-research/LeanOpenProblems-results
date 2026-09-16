import Submission.Spec
open Nat Finset

#eval (List.range 50).map (fun n =>
  if h : n = 0 then true else
    let numerator_int : ℤ := Finset.sum (range (n + 1)) fun k => (T_term k : ℤ) * (T_term (n - k) : ℤ)
    let denominator : ℤ := ((2 * n : ℤ) - 1) * ((3 * n).choose n : ℤ)
    denominator ∣ numerator_int
)
