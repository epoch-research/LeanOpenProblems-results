import FormalConjectures.Util.ProblemImports

def rNat (a b : Nat) := True
inductive J : Quot rNat → Type where
| z : J (Quot.mk rNat 0)

#check J.z
#check Quot.sound (r:=rNat) (a:=0) (b:=1) True.intro

def j1 : J (Quot.mk rNat 1) := by
  exact Eq.mp (congrArg J (Quot.sound (r:=rNat) (a:=0) (b:=1) True.intro)) J.z

#print j1
#check J.noConfusion
-- Can we eliminate j1? Cases should maybe turn quotient equality into impossible? try
example : False := by
  cases j1
  -- goal?
  simp at *
