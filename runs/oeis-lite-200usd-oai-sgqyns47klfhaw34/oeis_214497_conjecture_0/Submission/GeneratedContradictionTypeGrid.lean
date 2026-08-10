import FormalConjectures.Util.ProblemImports

-- A grid of candidate concrete types for contradictory instances.
-- If any branch works, this would prove False soundly; otherwise Lean reports first unsolved failing branch.
example : False := by
  first
  | exact false_of_nontrivial_of_subsingleton Empty
  | exact false_of_nontrivial_of_subsingleton PEmpty
  | exact false_of_nontrivial_of_subsingleton PUnit
  | exact false_of_nontrivial_of_subsingleton Unit
  | exact false_of_nontrivial_of_subsingleton Bool
  | exact false_of_nontrivial_of_subsingleton Prop
  | exact false_of_nontrivial_of_subsingleton (Fin 0)
  | exact false_of_nontrivial_of_subsingleton (Fin 1)
  | exact false_of_nontrivial_of_subsingleton (Fin 2)
  | exact false_of_nontrivial_of_subsingleton (ULift Empty)
  | exact false_of_nontrivial_of_subsingleton (ULift PUnit)
  | exact false_of_nontrivial_of_subsingleton (PLift Empty)
  | exact false_of_nontrivial_of_subsingleton (PLift PUnit)
  | exact false_of_nontrivial_of_subsingleton (Option Empty)
  | exact false_of_nontrivial_of_subsingleton (Option PUnit)
  | exact false_of_nontrivial_of_subsingleton (List Empty)
  | exact false_of_nontrivial_of_subsingleton (List PUnit)
  | exact false_of_nontrivial_of_subsingleton (Subtype (fun x : ℕ => x = 0))
  | exact false_of_nontrivial_of_subsingleton (Subtype (fun x : Bool => True))
  | exact not_finite Empty
  | exact not_finite PEmpty
  | exact not_finite PUnit
  | exact not_finite Unit
  | exact not_finite Bool
  | exact not_finite Prop
  | exact not_finite (Fin 0)
  | exact not_finite (Fin 1)
  | exact not_finite (Fin 2)
  | exact not_finite (ULift ℕ)
  | exact not_finite (PLift ℕ)
  | exact not_finite (Option ℕ)
  | exact not_finite (List PUnit)
  | exact not_finite (ℕ × Empty)
  | exact not_finite (Empty → ℕ)
  | exact not_finite (PUnit → ℕ)
  | exact CharP.false_of_nontrivial_of_char_one (R := ZMod 1)
  | exact CharP.false_of_nontrivial_of_char_one (R := ZMod 0)
  | exact CharP.false_of_nontrivial_of_char_one (R := PUnit)
