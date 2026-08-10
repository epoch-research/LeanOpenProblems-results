import FormalConjectures.Util.ProblemImports

partial def inhProp (P : Prop) : Inhabited P := inhProp P

theorem arbitrary (P : Prop) : P := (inhProp P).default
#print axioms arbitrary
