import FormalConjectures.Util.ProblemImports

#check LTSeries.nonempty_of_finiteDimensionalOrder
#check RelSeries.nonempty_of_finiteDimensional
#check LTSeries.nonempty_of_infiniteDimensionalOrder
#check RelSeries.nonempty_of_infiniteDimensional

example : Nonempty Empty := LTSeries.nonempty_of_finiteDimensionalOrder Empty
example : False := nomatch (Classical.choice (LTSeries.nonempty_of_finiteDimensionalOrder Empty))
#print axioms _example
