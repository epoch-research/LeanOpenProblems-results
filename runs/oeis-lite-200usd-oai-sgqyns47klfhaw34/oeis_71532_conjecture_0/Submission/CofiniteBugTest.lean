import FormalConjectures.Util.ProblemImports
open Filter

#check cofinite_eq_atTop
#print axioms cofinite_eq_atTop

-- Test on Fin 1? Need orderbot/locallyfinite instances.
example : False := by
  have h := cofinite_eq_atTop (α := Fin 1)
  -- If false, perhaps atTop contains {0}, cofinite contains empty?
  -- cofinite on finite type is bottom? Let's see simp.
  have hempty : (∅ : Set (Fin 1)) ∈ (cofinite : Filter (Fin 1)) := by simp [cofinite]
  rw [h] at hempty
  simpa using hempty
