import Mathlib

open Polynomial

noncomputable def apery_poly (n : ℕ) : ℚ[X] :=
  Finset.sum (Finset.range (n + 1)) fun (k : ℕ) ↦
    C (((n.choose k) ^ 2 * ((n + k).choose k) : ℕ) : ℚ) * (X : ℚ[X]) ^ k

inductive MyProp (n : ℕ) : Type where
  | mk1 : (PLift (Irreducible (apery_poly n)) ⊕ MyProp n) → MyProp n
  | mk2 : (PLift (¬(Irreducible (apery_poly n))) ⊕ MyProp n) → MyProp n

noncomputable instance (n : ℕ) : Nonempty (MyProp n) := by
  by_cases h : Irreducible (apery_poly n)
  · exact ⟨MyProp.mk1 (Sum.inl (PLift.up h))⟩
  · exact ⟨MyProp.mk2 (Sum.inl (PLift.up h))⟩

noncomputable instance (n : ℕ) : Inhabited (MyProp n) :=
  Classical.inhabited_of_nonempty (inferInstance)

partial def get_myProp (n : ℕ) : MyProp n :=
  MyProp.mk1 (Sum.inr (get_myProp n))

partial def get_irr (n : ℕ) (h : MyProp n) : PLift (Irreducible (apery_poly n)) ⊕ Unit :=
  match h with
  | MyProp.mk1 (Sum.inl x) => Sum.inl x
  | MyProp.mk1 (Sum.inr y) => get_irr n y
  | MyProp.mk2 _ => Sum.inr ()
