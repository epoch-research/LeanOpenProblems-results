import FormalConjectures.Util.ProblemImports

def QP := Quot (fun (_ _ : Prop) => True)

def holds (q : QP) : Prop := by
  induction q using Quot.ind with
  | h P => exact P

example : holds (Quot.mk (fun (_ _ : Prop) => True) True : QP) := by
  change True
  trivial

example : False := by
  have hq : (Quot.mk (fun (_ _ : Prop) => True) True : QP) = Quot.mk (fun (_ _ : Prop) => True) False := Quot.sound trivial
  have ht : holds (Quot.mk (fun (_ _ : Prop) => True) True : QP) := by trivial
  rw [hq] at ht
  exact ht
#print axioms QuotPropOutTest._example_1
