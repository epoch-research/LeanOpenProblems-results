import Mathlib

open Polynomial

noncomputable def apery_poly (n : ℕ) : ℚ[X] :=
  Finset.sum (Finset.range (n + 1)) fun (k : ℕ) ↦
    C (((n.choose k) ^ 2 * ((n + k).choose k) : ℕ) : ℚ) * (X : ℚ[X]) ^ k

unsafe def unsafe_fun (n : ℕ) : Inhabited (Irreducible (apery_poly n)) ⊕ PUnit :=
  Sum.inr PUnit.unit

@[implemented_by unsafe_fun]
opaque get_sum (n : ℕ) : Inhabited (Irreducible (apery_poly n)) ⊕ PUnit

#print axioms get_sum
