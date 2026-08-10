import FormalConjectures.Util.ProblemImports
theorem qout_true : Quot.out (Quot.mk (fun (_ _ : Prop) => True) True) := by
  exact True.intro
#print axioms qout_true
