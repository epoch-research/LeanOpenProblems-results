import FormalConjectures.Util.ProblemImports

abbrev QNat := Quot (fun _ _ : Nat => True)
def qn (n : Nat) : QNat := Quot.mk _ n

inductive J : QNat → Type where
| c0 : J (qn 0)

def x : J (qn 1) := Eq.mp (congrArg J (by exact Quot.sound trivial : qn 0 = qn 1)) J.c0

example : False := by
  nomatch x

#print axioms x
#print axioms _example
