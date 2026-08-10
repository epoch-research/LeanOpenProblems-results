import Mathlib

open Polynomial

noncomputable def apery_poly (n : ℕ) : ℚ[X] :=
  Finset.sum (Finset.range (n + 1)) fun (k : ℕ) ↦
    C (((n.choose k) ^ 2 * ((n + k).choose k) : ℕ) : ℚ) * (X : ℚ[X]) ^ k

theorem apery_poly_1_eq : apery_poly 1 = 1 + C 2 * X := by
  unfold apery_poly
  ext m
  simp [Finset.sum_range_succ]

theorem apery_poly_1_irreducible : Irreducible (apery_poly 1) := by
  rw [apery_poly_1_eq]
  apply irreducible_of_degree_eq_one
  compute_degree!

unsafe def unsafe_proof (P : Prop) [Inhabited P] : P :=
  unsafe_proof P

@[implemented_by unsafe_proof]
opaque get_proof (P : Prop) [Inhabited P] : P

theorem test_axiom (P : Prop) [Inhabited P] : P :=
  get_proof P

def MyProp (n : ℕ) : Prop := Irreducible (apery_poly n)

attribute [irreducible] MyProp

noncomputable def inst_aux (n : ℕ) (hn : 1 ≤ n) : Inhabited (MyProp n) :=
  match n with
  | 0 => by omega
  | 1 =>
    have : Irreducible (apery_poly 1) := apery_poly_1_irreducible
    -- we can cast this to MyProp 1
    ⟨by
      unfold MyProp
      exact apery_poly_1_irreducible⟩
  | n + 2 =>
    have : 1 ≤ n + 1 := by omega
    ⟨@test_axiom (MyProp (n + 2)) (inst_aux (n + 1) this)⟩

#print axioms inst_aux
