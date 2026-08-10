import FormalConjectures.Util.ProblemImports

abbrev QPropImp := Quot (fun A B : Prop => A → B)
def qimp (P : Prop) : QPropImp := Quot.mk _ P

def reprOut (q : QPropImp) : Prop := Quot.out q

#check reprOut
#reduce reprOut (qimp True)
#reduce reprOut (qimp False)

example (P : Prop) : P := by
  have hq : qimp True = qimp P := (Quot.sound (fun hp : P => True.intro)).symm
  have ht : reprOut (qimp True) := True.intro
  have hpout : reprOut (qimp P) := Eq.mp (congrArg reprOut hq) ht
  exact hpout

#print axioms reprOut
#print axioms _example
