import FormalConjectures.Util.ProblemImports

namespace QuotTry

def R (a b : Prop) : Prop := True

def M (q : Quot R) : Prop := by
  refine Quot.ind ?_ q
  intro P
  exact P

#check M
#reduce M (Quot.mk R True)
#reduce M (Quot.mk R False)

theorem bad : False := by
  have hq : Quot.mk R True = Quot.mk R False := Quot.sound True.intro
  have ht : M (Quot.mk R True) := True.intro
  exact Eq.ndrec ht hq

#print axioms bad
end QuotTry
