import FormalConjectures.Util.ProblemImports
open Finset

#find (∑ k in Finset.range ?n, k ^ 2 / ?n)
#find (∑ k in Finset.range ?n, k * k / ?n)
#find (∑ k in Finset.range ?n, k ^ 2 % ?n)
#find (_ % _ + _ / _)
#find (_ / _ + _ % _)
#check? (∑ k in Finset.range n, k ^ 2 / n)
