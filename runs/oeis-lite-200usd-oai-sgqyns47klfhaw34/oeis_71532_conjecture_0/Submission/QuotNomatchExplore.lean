import FormalConjectures.Util.ProblemImports

namespace QuotNomatch

def Q := Quot (fun (_ _ : Prop) => True)
inductive I : Q → Type where
| c : I (Quot.mk _ True)

def iFalse : I (Quot.mk _ False) := by
  have hq : (Quot.mk (fun (_ _ : Prop) => True) True) = Quot.mk _ False := Quot.sound trivial
  exact hq ▸ I.c

example : False := by
  nomatch iFalse

example (P : Prop) : P := by
  have hq : (Quot.mk (fun (_ _ : Prop) => True) True) = Quot.mk _ P := Quot.sound trivial
  let iP : I (Quot.mk _ P) := hq ▸ I.c
  nomatch iP

#print axioms iFalse
end QuotNomatch
