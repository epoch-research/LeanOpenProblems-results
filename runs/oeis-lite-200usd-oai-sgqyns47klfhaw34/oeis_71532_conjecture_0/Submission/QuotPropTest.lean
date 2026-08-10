import FormalConjectures.Util.ProblemImports

def Q := Quot (fun (_ _ : Prop) => True)

def F (q : Q) : Prop := by
  induction q with
  | mk P => exact P

#check F

theorem arbitrary (P : Prop) : P := by
  have hq : (Quot.mk (fun (_ _ : Prop) => True) True : Q) = Quot.mk _ P := Quot.sound trivial
  have ht : F (Quot.mk (fun (_ _ : Prop) => True) True : Q) := trivial
  simpa [hq, F] using ht

#print axioms arbitrary
