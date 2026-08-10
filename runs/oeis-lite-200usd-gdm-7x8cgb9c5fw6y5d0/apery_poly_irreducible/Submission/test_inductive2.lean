import Mathlib

open Polynomial

noncomputable def apery_poly (n : ℕ) : ℚ[X] :=
  Finset.sum (Finset.range (n + 1)) fun (k : ℕ) ↦
    C (((n.choose k) ^ 2 * ((n + k).choose k) : ℕ) : ℚ) * (X : ℚ[X]) ^ k

inductive MyType (n : ℕ)
  | mk : (Inhabited (Irreducible (apery_poly n)) → MyType n) → MyType n

partial def get_myType (n : ℕ) : MyType n :=
  MyType.mk (fun _ => get_myType n)

instance (n : ℕ) : Inhabited (MyType n) := ⟨get_myType n⟩

#print axioms get_myType
