import FormalConjectures.Util.ProblemImports

#synth LocallyFiniteOrderBot (WithTop ℕ)
#synth Fintype (Set.univ ∩ Set.Iio (⊤ : WithTop ℕ) : Set (WithTop ℕ))
#synth Infinite (Set.univ ∩ Set.Iio (⊤ : WithTop ℕ) : Set (WithTop ℕ))

example : False := by
  exact Fintype.false (α := (Set.univ ∩ Set.Iio (⊤ : WithTop ℕ) : Set (WithTop ℕ))) inferInstance

#synth LocallyFiniteOrderBot (WithBot ℕ)
#synth Fintype (Set.univ ∩ Set.Iio ((0:ℕ) : WithBot ℕ) : Set (WithBot ℕ))
#synth Infinite (Set.univ ∩ Set.Iio (⊤ : WithBot ℕ) : Set (WithBot ℕ))
