import FormalConjectures.Util.ProblemImports
open CategoryTheory CategoryTheory.Limits

-- finite + infinite accidental combos
#synth Fintype (Set.univ ∩ Set.Iio (5:ℕ) : Set ℕ)
#synth Infinite (Set.univ ∩ Set.Iio (5:ℕ) : Set ℕ)
#synth Finite ℚ
#synth Fintype ℚ
#synth Infinite (Fin 0)
#synth Infinite (Fin 1)
#synth Infinite (Set.Iio (5:ℕ))

-- simple zero candidates
#synth Simple (0 : ModuleCat ℚ)
#synth Simple (0 : Type u)
#synth Simple (0 : AddCommGrp)
#synth Simple (0 : RingCat)
