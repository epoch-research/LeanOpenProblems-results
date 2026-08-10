import FormalConjectures.Util.ProblemImports
open Nat Finset ArithmeticFunction

-- Is there a lemma: (zeta * f) n = sum over divisors of f?
#check @ArithmeticFunction.coe_zeta_mul_apply
#check @ArithmeticFunction.coe_mul_zeta_apply
-- valuation of sum lemmas
#check @padicValRat.lt_iff
example : True := trivial
