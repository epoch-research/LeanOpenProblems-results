import FormalConjectures.Util.ProblemImports
open Nat Finset
noncomputable def a (n : ℕ) : ℕ :=
  Rat.den <| (Nat.divisors n).sum fun d => (1 : Rat) / (ArithmeticFunction.sigma 1 d : Rat)

set_option maxRecDepth 8000 in
theorem rev494 : a 494 = 2 := by
  have hd : Nat.divisors 494 = {1, 2, 13, 19, 26, 38, 247, 494} := by decide
  unfold a; rw [hd]
  norm_num [Finset.sum_insert,
    show ArithmeticFunction.sigma 1 1 = 1 from by decide,
    show ArithmeticFunction.sigma 1 2 = 3 from by decide,
    show ArithmeticFunction.sigma 1 13 = 14 from by decide,
    show ArithmeticFunction.sigma 1 19 = 20 from by decide,
    show ArithmeticFunction.sigma 1 26 = 42 from by decide,
    show ArithmeticFunction.sigma 1 38 = 60 from by decide,
    show ArithmeticFunction.sigma 1 247 = 280 from by decide,
    show ArithmeticFunction.sigma 1 494 = 840 from by decide]
#print axioms rev494
