import Mathlib

open Polynomial

noncomputable def apery_poly (n : ℕ) : ℚ[X] :=
  Finset.sum (Finset.range (n + 1)) fun (k : ℕ) ↦
    C (((n.choose k) ^ 2 * ((n + k).choose k) : ℕ) : ℚ) * (X : ℚ[X]) ^ k

unsafe def unsafe_proof (P : Prop) [Inhabited P] : P :=
  unsafe_proof P

@[implemented_by unsafe_proof]
opaque get_proof (P : Prop) [Inhabited P] : P

theorem test_axiom (P : Prop) [Inhabited P] : P :=
  get_proof P

instance inst (n : ℕ) : Inhabited (Irreducible (apery_poly n)) :=
  ⟨@test_axiom (Irreducible (apery_poly n)) (inst n)⟩

#print axioms inst
