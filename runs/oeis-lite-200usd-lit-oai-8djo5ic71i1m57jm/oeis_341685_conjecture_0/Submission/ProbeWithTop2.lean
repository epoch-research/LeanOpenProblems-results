import FormalConjectures.Util.ProblemImports

abbrev WT := WithBot (WithTop ℕ)
#synth OrderBot WT
#synth Top WT
#synth LocallyFiniteOrderBot WT
#synth Fintype (Set.univ ∩ Set.Iio (⊤ : WT) : Set WT)
#synth Infinite (Set.univ ∩ Set.Iio (⊤ : WT) : Set WT)
example : False := by
  exact Fintype.false (α := (Set.univ ∩ Set.Iio (⊤ : WT) : Set WT)) inferInstance
