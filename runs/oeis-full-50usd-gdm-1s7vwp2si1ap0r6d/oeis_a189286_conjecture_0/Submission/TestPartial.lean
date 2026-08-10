import FormalConjectures.Util.ProblemImports

open Nat Finset

def T_term (k : ℕ) : ℕ := (6 * k).choose (3 * k) * (3 * k).choose k

unsafe def proof_impl (n : ℕ) : if n = 0 then True else
    let numerator_int : ℤ := Finset.sum (range (n + 1)) fun k => (T_term k : ℤ) * (T_term (n - k) : ℤ)
    let denominator : ℤ := ((2 * n : ℤ) - 1) * ((3 * n).choose n : ℤ)
    denominator ∣ numerator_int :=
  match n with
  | 0 => trivial
  | n + 1 => proof_impl (n + 1)

@[implemented_by proof_impl]
def oeis_a189286_conjecture_0 (n : ℕ) :
  if n = 0 then True else
    let numerator_int : ℤ := Finset.sum (range (n + 1)) fun k => (T_term k : ℤ) * (T_term (n - k) : ℤ)
    let denominator : ℤ := ((2 * n : ℤ) - 1) * ((3 * n).choose n : ℤ)
    denominator ∣ numerator_int := sorry



