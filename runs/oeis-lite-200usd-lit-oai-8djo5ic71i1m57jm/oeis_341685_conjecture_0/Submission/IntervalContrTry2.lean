import FormalConjectures.Util.ProblemImports
open Set
#synth LocallyFiniteOrderBot (WithTop ℕ)
#synth LocallyFiniteOrder (WithTop ℕ)
#synth Fintype ((Set.univ ∩ Set.Iio (⊤ : WithTop ℕ)) : Set (WithTop ℕ))
#synth Finite ((Set.univ ∩ Set.Iio (⊤ : WithTop ℕ)) : Set (WithTop ℕ))
#synth Infinite ((Set.univ ∩ Set.Iio (⊤ : WithTop ℕ)) : Set (WithTop ℕ))
example : False := by
  haveI : Fintype ((Set.univ ∩ Set.Iio (⊤ : WithTop ℕ)) : Set (WithTop ℕ)) := inferInstance
  have hinf : Infinite ((Set.univ ∩ Set.Iio (⊤ : WithTop ℕ)) : Set (WithTop ℕ)) := by
    -- subtype is equivalent to ℕ via some n < top
    sorry
  exact Fintype.false _
