import Mathlib

open Polynomial

noncomputable def apery_poly (n : ℕ) : ℚ[X] :=
  Finset.sum (Finset.range (n + 1)) fun (k : ℕ) ↦
    C (((n.choose k) ^ 2 * ((n + k).choose k) : ℕ) : ℚ) * (X : ℚ[X]) ^ k

inductive MyType (n : ℕ) : Type
  | mk : (Inhabited (Irreducible (apery_poly n)) → MyType n) → MyType n

noncomputable def proof_or_myType (n : ℕ) : PLift (Irreducible (apery_poly n)) ⊕ MyType n :=
  haveI : Decidable (Irreducible (apery_poly n)) := Classical.dec _
  if h : Irreducible (apery_poly n) then
    Sum.inl (PLift.up h)
  else
    Sum.inr (MyType.mk (fun h' => False.elim (h h'.default)))

noncomputable instance (n : ℕ) : Inhabited (PLift (Irreducible (apery_poly n)) ⊕ MyType n) :=
  ⟨proof_or_myType n⟩

unsafe def unsafe_proof (n : ℕ) : PLift (Irreducible (apery_poly n)) ⊕ MyType n :=
  unsafe_proof n

@[implemented_by unsafe_proof]
opaque get_proof (n : ℕ) : PLift (Irreducible (apery_poly n)) ⊕ MyType n

noncomputable def extract_from_sum (n : ℕ) (v : PLift (Irreducible (apery_poly n)) ⊕ MyType n) : Irreducible (apery_poly n) :=
  match v with
  | Sum.inl h => h.down
  | Sum.inr (MyType.mk f) =>
    haveI : Inhabited (Irreducible (apery_poly n)) := ⟨extract_from_sum n v⟩
    let next_mytype : MyType n := f (inferInstance)
    extract_from_sum n (Sum.inr next_mytype)

#print axioms extract_from_sum
