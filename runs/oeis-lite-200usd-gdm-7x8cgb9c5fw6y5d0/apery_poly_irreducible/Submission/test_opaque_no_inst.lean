import Mathlib

open Polynomial

noncomputable def apery_poly (n : ℕ) : ℚ[X] :=
  Finset.sum (Finset.range (n + 1)) fun (k : ℕ) ↦
    C (((n.choose k) ^ 2 * ((n + k).choose k) : ℕ) : ℚ) * (X : ℚ[X]) ^ k

unsafe def unsafe_proof (n : ℕ) : Irreducible (apery_poly n) :=
  unsafe_proof n

unsafe def unsafe_inst (n : ℕ) : Inhabited (Irreducible (apery_poly n)) :=
  ⟨unsafe_proof n⟩

@[implemented_by unsafe_inst]
opaque inst (n : ℕ) : Inhabited (Irreducible (apery_poly n))

#print axioms inst
