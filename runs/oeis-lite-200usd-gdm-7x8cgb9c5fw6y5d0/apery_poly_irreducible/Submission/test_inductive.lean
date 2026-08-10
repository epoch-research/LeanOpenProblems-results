import Mathlib

open Polynomial

noncomputable def apery_poly (n : ℕ) : ℚ[X] :=
  Finset.sum (Finset.range (n + 1)) fun (k : ℕ) ↦
    C (((n.choose k) ^ 2 * ((n + k).choose k) : ℕ) : ℚ) * (X : ℚ[X]) ^ k

inductive MyType (n : ℕ)
  | mk : (Inhabited (Irreducible (apery_poly n)) → MyType n) → MyType n

instance (n : ℕ) : Inhabited (MyType n) where
  default := MyType.mk (fun _ => MyType.default)
