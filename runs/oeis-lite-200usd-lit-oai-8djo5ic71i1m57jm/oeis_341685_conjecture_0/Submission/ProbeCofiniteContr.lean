import FormalConjectures.Util.ProblemImports
open Filter

#check cofinite_eq_atTop
#check cofinite_hasBasis_Ioi

example : False := by
  have h := (cofinite_eq_atTop (α := Fin 1))
  -- cofinite on finite type is bottom? atTop pure top; maybe show empty/eventually false
  have hfalse : (∀ᶠ x : Fin 1 in (cofinite : Filter (Fin 1)), False) := by
    simp [Filter.eventually_cofinite]
  rw [h] at hfalse
  -- atTop on Fin 1 should not eventually false
  simp at hfalse

example : False := by
  have h := (cofinite_eq_atTop (α := Fin 2))
  have hfalse : (∀ᶠ x : Fin 2 in (cofinite : Filter (Fin 2)), False) := by
    simp [Filter.eventually_cofinite]
  rw [h] at hfalse
  simp at hfalse
