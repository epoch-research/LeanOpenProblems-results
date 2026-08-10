import FormalConjectures.Util.ProblemImports
open Nat Finset ArithmeticFunction

-- explore: is the sum expressible as a Dirichlet convolution / multiplicative?
example : True := by
  trivial

-- search for relevant lemmas
open ArithmeticFunction in
#check @ArithmeticFunction.IsMultiplicative
#check @ArithmeticFunction.isMultiplicative_sigma
#check @ArithmeticFunction.IsMultiplicative.mul
-- padic valuation of rationals
#check @padicValRat
#check @Rat.den
