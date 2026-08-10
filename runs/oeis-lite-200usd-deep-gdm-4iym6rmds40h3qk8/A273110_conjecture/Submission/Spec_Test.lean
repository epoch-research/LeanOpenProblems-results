import FormalConjectures.Util.ProblemImports

example (P : Prop) (h : Nonempty P) : P := Classical.choice h
