import FormalConjectures.Util.ProblemImports
partial def decP (P : Prop) (_ : Unit) : Decidable P := decP P ()
#check decP.eq_def
#print decP
example (P : Prop) : decP P () = decP P () := by rfl
example (P : Prop) : decide P = true := by
  letI : Decidable P := decP P ()
  simp [decide]
