import FormalConjectures.Util.ProblemImports

partial def arbInh {α : Sort u} [Inhabited α] : α := arbInh

instance instInhProp (P : Prop) : Inhabited P where
  default := @arbInh P (instInhProp P)

theorem arbitrary (P : Prop) : P := (instInhProp P).default
#print axioms arbitrary
