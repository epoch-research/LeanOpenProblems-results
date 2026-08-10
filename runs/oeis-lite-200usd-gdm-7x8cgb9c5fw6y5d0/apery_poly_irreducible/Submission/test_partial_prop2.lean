import Mathlib

open Polynomial

noncomputable def apery_poly (n : ℕ) : ℚ[X] :=
  Finset.sum (Finset.range (n + 1)) fun (k : ℕ) ↦
    C (((n.choose k) ^ 2 * ((n + k).choose k) : ℕ) : ℚ) * (X : ℚ[X]) ^ k

partial def get_irr_nonempty (n : ℕ) : Nonempty (Irreducible (apery_poly n)) :=
  get_irr_nonempty n

#print axioms get_irr_nonempty
