import FormalConjectures.Util.ProblemImports

def Q := Quot (fun P Q : Prop => P → Q)
def q (P:Prop) : Q := Quot.mk _ P
#reduce Quot.out (q True)
#reduce Quot.out (q False)
#check Quot.out_eq (q True)
example : Quot.out (q True) := by
  -- try exact True.intro
  native_decide
