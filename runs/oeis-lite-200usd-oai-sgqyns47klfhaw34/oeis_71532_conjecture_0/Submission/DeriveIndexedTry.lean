import FormalConjectures.Util.ProblemImports
inductive Bad : Prop → Type where
| mk : Bad True
deriving instance Inhabited for Bad
#synth Inhabited (Bad False)
def badFalse : Bad False := default
#print axioms badFalse
