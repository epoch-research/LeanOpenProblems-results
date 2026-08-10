import FormalConjectures.Util.ProblemImports
open Set
#check ENat
#synth LocallyFiniteOrderBot ENat
#synth LocallyFiniteOrder ENat
#synth Fintype ((Set.univ ∩ Set.Iio (⊤ : ENat)) : Set ENat)
#synth Finite ((Set.univ ∩ Set.Iio (⊤ : ENat)) : Set ENat)
#synth Infinite ((Set.univ ∩ Set.Iio (⊤ : ENat)) : Set ENat)
