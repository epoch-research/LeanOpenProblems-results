import FormalConjectures.Util.ProblemImports

def R (_ _ : Prop) := True
def Q := Quot R
def qT : Q := Quot.mk R True
def qF : Q := Quot.mk R False
#check Quot.out
#check Quot.out_eq
#check Quot.mk_out
#check Quot.out_eq'
#reduce Quot.out qT
#reduce Quot.out qF
example : qT = qF := Quot.sound True.intro
example : Quot.out qT = True := by native_decide
example : Quot.out qF = False := by native_decide
-- can we prove in kernel?
example : Quot.out qT = True := by rfl
example : Quot.out qF = False := by rfl
