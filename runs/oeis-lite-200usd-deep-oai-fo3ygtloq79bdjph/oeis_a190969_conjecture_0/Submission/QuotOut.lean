import FormalConjectures.Util.ProblemImports

def q : Quot (fun (_ _ : Prop) => True) := Quot.mk _ True
#check Quot.out q
#print axioms Quot.out
example : (Quot.out q) := by
  dsimp [q]
  sorry
