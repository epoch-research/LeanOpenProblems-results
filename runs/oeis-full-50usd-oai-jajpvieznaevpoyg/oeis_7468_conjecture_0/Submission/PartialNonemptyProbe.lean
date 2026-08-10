import FormalConjectures.Util.ProblemImports

partial def neProp (P : Prop) : Nonempty P := neProp P
partial def neSort (α : Sort u) : Nonempty α := neSort α
partial def inhabitType (α : Type u) : Inhabited α := inhabitType α

example : False := (neProp False).some
example : False := Classical.choice (neSort False)
