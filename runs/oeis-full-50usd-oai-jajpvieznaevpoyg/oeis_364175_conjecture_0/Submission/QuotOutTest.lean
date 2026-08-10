import FormalConjectures.Util.ProblemImports
#check Quot.out
#check Quot.out_eq
#check Quot.exists_rep

universe u
def QSort := Quot (fun _ _ : Type u => True)

def qUnit : QSort := Quot.mk _ PUnit
def qEmpty : QSort := Quot.mk _ PEmpty
example : qUnit = qEmpty := Quot.sound trivial
#check congrArg Quot.out (show qUnit = qEmpty from Quot.sound trivial)
#check Quot.out_eq qUnit
#check Quot.out_eq qEmpty
