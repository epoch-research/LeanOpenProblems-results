import FormalConjectures.Util.ProblemImports

partial def inh (α : Sort u) : Inhabited α := inh α
#print axioms inh
example : False := (inh False).default
#print axioms PartialInhabitedExp._example_1

partial def nonemp (α : Sort u) : Nonempty α := nonemp α
#print axioms nonemp
example : False := Classical.choice (nonemp False)
#print axioms PartialInhabitedExp._example_2

partial def subs (α : Sort u) : Subsingleton α := subs α
#print axioms subs
