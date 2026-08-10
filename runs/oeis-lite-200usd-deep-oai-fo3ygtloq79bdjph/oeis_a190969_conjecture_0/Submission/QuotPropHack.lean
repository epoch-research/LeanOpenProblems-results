import FormalConjectures.Util.ProblemImports

noncomputable def qprop (P : Prop) : Quot (fun (_ _ : Prop) => True) := Quot.mk _ P
noncomputable def mot (q : Quot (fun (_ _ : Prop) => True)) : Prop := Quot.out q

example (P : Prop) : P := by
  let h : qprop True = qprop P := Quot.sound trivial
  change mot (qprop P)
  rw [← h]
  change mot (qprop True)
  dsimp [mot, qprop]
  -- goal Quot.out (Quot.mk (fun x x_1 => True) True)
  -- try exact True.intro
  exact True.intro
