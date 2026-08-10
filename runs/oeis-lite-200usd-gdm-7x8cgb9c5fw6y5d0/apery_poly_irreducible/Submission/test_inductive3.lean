import Mathlib

open Polynomial

noncomputable def apery_poly (n : ℕ) : ℚ[X] :=
  Finset.sum (Finset.range (n + 1)) fun (k : ℕ) ↦
    C (((n.choose k) ^ 2 * ((n + k).choose k) : ℕ) : ℚ) * (X : ℚ[X]) ^ k

inductive MyType (n : ℕ)
  | mk : (Inhabited (Irreducible (apery_poly n)) → MyType n) → MyType n

noncomputable def proof_or_myType (n : ℕ) : Irreducible (apery_poly n) ⊕ MyType n :=
  if h : Irreducible (apery_poly n) then
    Sum.inl h
  else
    Sum.inr (MyType.mk (fun h' => False.elim (h h'.default)))

noncomputable instance (n : ℕ) : Inhabited (Irreducible (apery_poly n) ⊕ MyType n) :=
  ⟨proof_or_myType n⟩
