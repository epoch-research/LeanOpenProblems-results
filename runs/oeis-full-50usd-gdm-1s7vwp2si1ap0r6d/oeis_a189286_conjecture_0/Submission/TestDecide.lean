import FormalConjectures.Util.ProblemImports

open Nat Finset

def T_term (k : ℕ) : ℕ := (6 * k).choose (3 * k) * (3 * k).choose k

theorem test_1 :
  let numerator_int : ℤ := Finset.sum (range (1 + 1)) fun k => (T_term k : ℤ) * (T_term (1 - k) : ℤ)
  let denominator : ℤ := ((2 * 1 : ℤ) - 1) * ((3 * 1).choose 1 : ℤ)
  denominator ∣ numerator_int := by decide

theorem test_2 :
  let numerator_int : ℤ := Finset.sum (range (2 + 1)) fun k => (T_term k : ℤ) * (T_term (2 - k) : ℤ)
  let denominator : ℤ := ((2 * 2 : ℤ) - 1) * ((3 * 2).choose 2 : ℤ)
  denominator ∣ numerator_int := by decide

theorem test_5 :
  let numerator_int : ℤ := Finset.sum (range (5 + 1)) fun k => (T_term k : ℤ) * (T_term (5 - k) : ℤ)
  let denominator : ℤ := ((2 * 5 : ℤ) - 1) * ((3 * 5).choose 5 : ℤ)
  denominator ∣ numerator_int := by decide

theorem test_10 :
  let numerator_int : ℤ := Finset.sum (range (10 + 1)) fun k => (T_term k : ℤ) * (T_term (10 - k) : ℤ)
  let denominator : ℤ := ((2 * 10 : ℤ) - 1) * ((3 * 10).choose 10 : ℤ)
  denominator ∣ numerator_int := by decide
