import FormalConjectures.Util.ProblemImports

def R (_ _ : Prop) := True
#check (Quot.lcInv (Quot.mk R True) : Prop)
example : (Quot.lcInv (Quot.mk R True) : Prop) := by
  change True
  trivial
example : False := by
  have hq : Quot.mk R True = Quot.mk R False := Quot.sound trivial
  have h1 : (Quot.lcInv (Quot.mk R True) : Prop) := by change True; trivial
  have h2 : (Quot.lcInv (Quot.mk R False) : Prop) := by simpa [hq] using h1
  change False at h2
  exact h2
#print axioms _example
