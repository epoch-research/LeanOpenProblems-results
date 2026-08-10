import FormalConjectures.Util.ProblemImports

open Nat Finset

def T_term (k : ℕ) : ℕ := (6 * k).choose (3 * k) * (3 * k).choose k

def PropToProve (n : ℕ) : Prop :=
  if n = 0 then True else
    let numerator_int : ℤ := Finset.sum (range (n + 1)) fun k => (T_term k : ℤ) * (T_term (n - k) : ℤ)
    let denominator : ℤ := ((2 * n : ℤ) - 1) * ((3 * n).choose n : ℤ)
    denominator ∣ numerator_int

def MyProp (n : ℕ) : Prop := answer(sorry)

theorem test_prop (n : ℕ) : MyProp n := by
  unfold MyProp
  trivial

#print axioms test_prop

theorem test_direct : ∀ (n : ℕ),
  if n = 0 then True else
    let numerator_int : ℤ := Finset.sum (range (n + 1)) fun k => (T_term k : ℤ) * (T_term (n - k) : ℤ)
    let denominator : ℤ := ((2 * n : ℤ) - 1) * ((3 * n).choose n : ℤ)
    denominator ∣ numerator_int := fun n => answer(sorry)

#print axioms test_direct






-- removed proof_helper













