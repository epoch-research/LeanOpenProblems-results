import FormalConjectures.Util.ProblemImports

def Q := Quot (fun P Q : Prop => P → Q)
def q (P:Prop) : Q := Quot.mk _ P

inductive I : Q → Prop where
| intro {P : Prop} : P → I (q P)

-- transport True proof to I(q P)
def inhabitI (P:Prop) : I (q P) := by
  have h : q True = q P := Eq.symm (Quot.sound (fun (_ : P) => True.intro))
  exact Eq.mp (congrArg I h) (I.intro True.intro)

-- try eliminate
theorem arb (P:Prop) : P := by
  have hI : I (q P) := inhabitI P
  cases hI with
  | intro h => exact h

#print axioms arb
