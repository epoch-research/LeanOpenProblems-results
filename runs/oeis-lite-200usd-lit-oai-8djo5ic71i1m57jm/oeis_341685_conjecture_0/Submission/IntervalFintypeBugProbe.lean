import FormalConjectures.Util.ProblemImports
#synth LocallyFiniteOrderBot ℕ∞
#synth LocallyFiniteOrder ℕ∞
#synth OrderBot ℕ∞
#synth Fintype ((Set.univ ∩ Set.Iio (⊤ : ℕ∞) : Set ℕ∞))
#synth Infinite ((Set.univ ∩ Set.Iio (⊤ : ℕ∞) : Set ℕ∞))
example : False := by
  exact Fintype.false ((inferInstance : Fintype ((Set.univ ∩ Set.Iio (⊤ : ℕ∞) : Set ℕ∞))))
