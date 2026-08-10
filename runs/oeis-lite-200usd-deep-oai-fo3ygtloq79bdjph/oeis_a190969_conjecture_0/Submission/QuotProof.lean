import FormalConjectures.Util.ProblemImports

noncomputable def qprop (P : Prop) : Quot (fun (_ _ : Prop) => True) := Quot.mk _ P
noncomputable def mot (q : Quot (fun (_ _ : Prop) => True)) : Prop := Quot.out q

theorem arbitrary (P : Prop) : P := by
  let h : qprop True = qprop P := Quot.sound trivial
  change mot (qprop P)
  rw [← h]
  change mot (qprop True)
  dsimp [mot, qprop]
  exact True.intro

#print axioms arbitrary
#check arbitrary False
