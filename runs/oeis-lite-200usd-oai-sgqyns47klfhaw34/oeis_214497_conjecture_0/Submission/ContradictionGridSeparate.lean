import FormalConjectures.Util.ProblemImports

set_option maxHeartbeats 50000

-- Each line is independent; all are expected to fail if library instances are consistent.
example : False := by exact false_of_nontrivial_of_subsingleton Empty
example : False := by exact false_of_nontrivial_of_subsingleton PEmpty
example : False := by exact false_of_nontrivial_of_subsingleton PUnit
example : False := by exact false_of_nontrivial_of_subsingleton Unit
example : False := by exact false_of_nontrivial_of_subsingleton Bool
example : False := by exact false_of_nontrivial_of_subsingleton Prop
example : False := by exact false_of_nontrivial_of_subsingleton (Fin 0)
example : False := by exact false_of_nontrivial_of_subsingleton (Fin 1)
example : False := by exact false_of_nontrivial_of_subsingleton (Fin 2)
example : False := by exact false_of_nontrivial_of_subsingleton (ULift Empty)
example : False := by exact false_of_nontrivial_of_subsingleton (ULift PUnit)
example : False := by exact false_of_nontrivial_of_subsingleton (PLift Empty)
example : False := by exact false_of_nontrivial_of_subsingleton (PLift PUnit)
example : False := by exact false_of_nontrivial_of_subsingleton (Option Empty)
example : False := by exact false_of_nontrivial_of_subsingleton (Option PUnit)
example : False := by exact false_of_nontrivial_of_subsingleton (List Empty)
example : False := by exact false_of_nontrivial_of_subsingleton (List PUnit)
example : False := by exact false_of_nontrivial_of_subsingleton (Subtype (fun x : ℕ => x = 0))
example : False := by exact false_of_nontrivial_of_subsingleton (Subtype (fun x : Bool => True))

example : False := by exact not_finite Empty
example : False := by exact not_finite PEmpty
example : False := by exact not_finite PUnit
example : False := by exact not_finite Unit
example : False := by exact not_finite Bool
example : False := by exact not_finite Prop
example : False := by exact not_finite (Fin 0)
example : False := by exact not_finite (Fin 1)
example : False := by exact not_finite (Fin 2)
example : False := by exact not_finite (ULift ℕ)
example : False := by exact not_finite (PLift ℕ)
example : False := by exact not_finite (Option ℕ)
example : False := by exact not_finite (List PUnit)
example : False := by exact not_finite (ℕ × Empty)
example : False := by exact not_finite (Empty → ℕ)
example : False := by exact not_finite (PUnit → ℕ)

example : False := by exact CharP.false_of_nontrivial_of_char_one (R := ZMod 1)
example : False := by exact CharP.false_of_nontrivial_of_char_one (R := ZMod 0)
