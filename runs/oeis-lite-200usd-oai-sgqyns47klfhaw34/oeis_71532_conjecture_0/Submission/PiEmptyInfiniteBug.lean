import FormalConjectures.Util.ProblemImports

#synth Fintype (Fin 0 → ℕ)
#synth Unique (Fin 0 → ℕ)
#synth Infinite (Fin 0 → ℕ)
#synth Nontrivial (Fin 0 → ℕ)

example : False := by
  haveI : Fintype (Fin 0 → ℕ) := inferInstance
  haveI : Infinite (Fin 0 → ℕ) := inferInstance
  exact Infinite.not_finite (α := Fin 0 → ℕ) inferInstance
