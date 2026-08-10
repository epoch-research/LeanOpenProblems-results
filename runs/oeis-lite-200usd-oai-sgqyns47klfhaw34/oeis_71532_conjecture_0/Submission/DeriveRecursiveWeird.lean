import FormalConjectures.Util.ProblemImports

inductive Bad1 where
| mk : (Bad1 → Empty) → Bad1
  deriving Nonempty

#check (inferInstance : Nonempty Bad1)

def elimBad1 : Bad1 -> Empty
| .mk f => f (.mk f)

example : False := nomatch elimBad1 (Classical.choice (inferInstance : Nonempty Bad1))
#print axioms Bad1.instNonempty
#print axioms elimBad1
#print axioms DeriveRecursiveWeird._example_1
