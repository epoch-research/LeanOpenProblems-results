import FormalConjectures.Util.ProblemImports

namespace QuotImpFamilyRec

def Q := Quot (fun (p q : Prop) => p → q)
inductive Fam : Q → Prop where
| intro (p : Prop) (hp : p) : Fam (Quot.mk _ p)

#check Fam.rec
#check Fam.casesOn

-- Nondependent eliminator to P: case has arbitrary p hp:p, cannot prove P.
def extractConst (P : Prop) (h : Fam (Quot.mk _ P)) : P := by
  refine Fam.rec (motive := fun q h => P) ?case h
  intro p hp
  exact ?_

end QuotImpFamilyRec
