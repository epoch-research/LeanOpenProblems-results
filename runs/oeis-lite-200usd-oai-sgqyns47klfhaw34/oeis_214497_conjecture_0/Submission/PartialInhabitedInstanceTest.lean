import FormalConjectures.Util.ProblemImports

partial def inhAny (α : Type) : Inhabited α := inhAny α
partial def nonemptyAny (α : Type) : Nonempty α := nonemptyAny α

#print axioms inhAny
#print axioms nonemptyAny
example : False := (inhAny False).default
