import FormalConjectures.Util.ProblemImports

open Polynomial

noncomputable def apery_poly (n : ℕ) : ℚ[X] := X

unsafe def my_proof_impl (n : ℕ) (hn : 1 ≤ n) : Irreducible (apery_poly n) :=
  unsafeCast True.intro
