import FormalConjectures.Util.ProblemImports

def R (_ _ : Prop) := True
def qT : Quot R := Quot.mk R True
def qF : Quot R := Quot.mk R False
#check Quotient.exact
#check Quot.exact
example : qT = qF := Quot.sound True.intro
example : R True False := Quot.exact (show qT = qF from Quot.sound True.intro)
-- any way to get True = False?
example : True = False := by
  have hq : qT = qF := Quot.sound True.intro
  -- exact Quotient.exact hq -- only R True False = True
  exact ?_
