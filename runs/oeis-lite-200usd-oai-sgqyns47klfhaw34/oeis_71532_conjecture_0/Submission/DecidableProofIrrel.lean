import FormalConjectures.Util.ProblemImports
axiom P : Prop
partial def decLoop (P : Prop) : Decidable P := decLoop P

-- Are all Decidable P values equal by proof irrelevance? No, Decidable P is Type, not Prop, but maybe Subsingleton?
#check (inferInstance : Subsingleton (Decidable P))
example : Subsingleton (Decidable P) := by infer_instance

example : P := by
  have hs : Subsingleton (Decidable P) := by infer_instance
  have heq : decLoop P = Decidable.isTrue (Classical.choice (show Nonempty P from ?_)) := Subsingleton.elim _ _
  exact ?_
