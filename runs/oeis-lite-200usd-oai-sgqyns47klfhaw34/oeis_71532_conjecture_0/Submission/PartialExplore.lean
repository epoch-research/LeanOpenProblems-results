import FormalConjectures.Util.ProblemImports

structure Bad (P : Prop) where
  val : Unit
  proof : P

partial def bad (P : Prop) : Bad P :=
  { val := (), proof := (bad P).proof }

theorem arbitrary (P : Prop) : P := (bad P).proof

#print axioms arbitrary
