import FormalConjectures.Util.ProblemImports

def Q := Quot (fun _ _ : Prop => True)
def q (P : Prop) : Q := Quot.mk _ P

inductive I : Q → Type where
| intro {P : Prop} : P → I (q P)

def inhabitI (P : Prop) : I (q P) := by
  have hq : q True = q P := Quot.sound True.intro
  exact Eq.mp (congrArg I hq) (I.intro True.intro)

example (P : Prop) : P := by
  have hI : I (q P) := inhabitI P
  cases hI with
  | intro h => exact h

#print axioms _example
