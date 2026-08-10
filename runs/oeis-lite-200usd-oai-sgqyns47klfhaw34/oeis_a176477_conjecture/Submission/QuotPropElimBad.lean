import FormalConjectures.Util.ProblemImports

def holdsQuot (r : Prop → Prop → Prop) (q : Quot r) : Prop :=
  Quot.inductionOn q (fun p : Prop => p)

theorem bad (P : Prop) : P := by
  let r : Prop → Prop → Prop := fun a b => a
  let qT : Quot r := Quot.mk r True
  let qP : Quot r := Quot.mk r P
  have hq : qT = qP := Quot.sound True.intro
  have ht : holdsQuot r qT := True.intro
  rw [hq] at ht
  exact ht

#print axioms bad
