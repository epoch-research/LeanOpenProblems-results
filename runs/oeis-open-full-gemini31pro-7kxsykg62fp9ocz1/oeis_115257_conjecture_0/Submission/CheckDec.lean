import Mathlib

open Polynomial

#check (inferInstance : Decidable (Irreducible (X : Polynomial ℚ)))
