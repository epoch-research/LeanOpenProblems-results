import FormalConjectures.Util.ProblemImports
example (n : ℕ) : n = n := by native_decide +revert
example : (∀ n : ℕ, n = n) := by
  classical
  exact fun n => rfl
#check Classical.dec
example : Decidable (∀ n : ℕ, n = n) := by infer_instance
example : Decidable (∀ n : ℕ, n = n) := Classical.dec _
