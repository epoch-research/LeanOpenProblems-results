import FormalConjectures.Util.ProblemImports
universe u
def QSort := Quot (fun _ _ : Type u => True)
def qUnit : QSort := Quot.mk _ PUnit
def qEmpty : QSort := Quot.mk _ PEmpty
#reduce Quot.out qUnit
#reduce Quot.out qEmpty
example : Quot.out qUnit = PUnit := rfl
example : Quot.out qEmpty = PEmpty := rfl
