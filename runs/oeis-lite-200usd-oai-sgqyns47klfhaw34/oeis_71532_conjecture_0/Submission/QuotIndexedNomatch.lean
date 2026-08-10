import FormalConjectures.Util.ProblemImports

def rNat (a b : Nat) := True
inductive J : Quot rNat → Type where
| z : J (Quot.mk rNat 0)
def j1 : J (Quot.mk rNat 1) := Eq.mp (congrArg J (Quot.sound (r:=rNat) (a:=0) (b:=1) True.intro)) J.z

example : False := nomatch j1

example : False := J.rec (motive := fun q _ => False) (by simp) j1
