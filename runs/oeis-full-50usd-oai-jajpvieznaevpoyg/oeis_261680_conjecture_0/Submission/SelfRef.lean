import FormalConjectures.Util.ProblemImports
inductive Bad : Prop | mk : Bad -> Bad
theorem bad : Bad := Bad.mk bad
#print axioms bad
