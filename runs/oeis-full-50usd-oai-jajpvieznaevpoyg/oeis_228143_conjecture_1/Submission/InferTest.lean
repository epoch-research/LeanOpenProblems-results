import FormalConjectures.Util.ProblemImports
open PowerSeries
#synth Nonempty (∃ C : PowerSeries ℤ, (PowerSeries.map (Int.castRingHom ℚ)) (C ^ 8) = (1 : PowerSeries ℚ))
#synth Inhabited (∃ C : PowerSeries ℤ, (PowerSeries.map (Int.castRingHom ℚ)) (C ^ 8) = (1 : PowerSeries ℚ))
