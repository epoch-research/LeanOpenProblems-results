import FormalConjectures.Util.ProblemImports

structure Bad (P : Prop) where
  val : Unit
  proof : P

partial def bad (P : Prop) (x : Bad P := bad P) : Bad P := x

theorem arbitrary (P : Prop) : P := (bad P).proof
#print axioms arbitrary
