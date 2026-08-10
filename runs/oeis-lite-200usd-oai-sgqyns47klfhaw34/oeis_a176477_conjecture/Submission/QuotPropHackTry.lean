import FormalConjectures.Util.ProblemImports

def QP := Quot (fun (_ _ : Prop) => True)

def out (q : QP) : Prop := Quot.liftOn q (fun p : Prop => p) (by
  intro a b h
  -- need a = b
  apply propext
  constructor <;> intro ha
  · exact ?x
  · exact ?y)

example : False := by
  have hq : (Quot.mk (fun (_ _ : Prop) => True) True : QP) = Quot.mk (fun (_ _ : Prop) => True) False := Quot.sound trivial
  have ht : out (Quot.mk (fun (_ _ : Prop) => True) True : QP) := by
    change True
    trivial
  rw [hq] at ht
  exact ht
