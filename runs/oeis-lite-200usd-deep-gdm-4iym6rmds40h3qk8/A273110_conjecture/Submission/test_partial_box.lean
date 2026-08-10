import FormalConjectures.Util.ProblemImports

structure MyBox (P : Prop) where
  val : Nonempty P
  deriving Nonempty

partial def my_partial_box (P : Prop) : MyBox P :=
  my_partial_box P

theorem my_theorem (P : Prop) : Nonempty P :=
  (my_partial_box P).val

#print axioms my_theorem
