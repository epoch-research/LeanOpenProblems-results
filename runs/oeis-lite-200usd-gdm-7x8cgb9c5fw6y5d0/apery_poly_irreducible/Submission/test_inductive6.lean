import Mathlib

open Polynomial

noncomputable def apery_poly (n : ℕ) : ℚ[X] :=
  Finset.sum (Finset.range (n + 1)) fun (k : ℕ) ↦
    C (((n.choose k) ^ 2 * ((n + k).choose k) : ℕ) : ℚ) * (X : ℚ[X]) ^ k

inductive MyType (n : ℕ) : Type
  | mk : (Inhabited (Irreducible (apery_poly n)) → MyType n) → MyType n

noncomputable def proof_or_myType (n : ℕ) : PLift (Irreducible (apery_poly n)) ⊕ MyType n :=
  Classical.byCases
    (p := Irreducible (apery_poly n))
    (fun h : Irreducible (apery_poly n) => Sum.inl (PLift.up h))
    (fun h : ¬ Irreducible (apery_poly n) => Sum.inr (MyType.mk (fun h' => False.elim (h h'.default))))

noncomputable instance (n : ℕ) : Inhabited (PLift (Irreducible (apery_poly n)) ⊕ MyType n) :=
  ⟨proof_or_myType n⟩
