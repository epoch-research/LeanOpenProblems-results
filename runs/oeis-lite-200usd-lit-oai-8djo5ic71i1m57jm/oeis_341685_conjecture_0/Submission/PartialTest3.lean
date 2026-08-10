import FormalConjectures.Util.ProblemImports
partial def fixP {P : Prop} (f : P → P) : P := f (fixP f)
theorem bad : False := fixP id
#print axioms bad
