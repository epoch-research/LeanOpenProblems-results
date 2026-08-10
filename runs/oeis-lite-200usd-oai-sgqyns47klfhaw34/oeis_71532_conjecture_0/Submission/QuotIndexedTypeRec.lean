import FormalConjectures.Util.ProblemImports

def Q := Quot (fun _ _ : Prop => True)
def q (P : Prop) : Q := Quot.mk _ P

inductive I : Q → Type where
| intro {P : Prop} : P → I (q P)

#check I.rec
#check I.recOn
#check I.casesOn

def inhabitI (P : Prop) : I (q P) := by
  have hq : q True = q P := Quot.sound True.intro
  exact Eq.mp (congrArg I hq) (I.intro True.intro)

-- try recursor with motive depending on index q and element = target P if q=qP? constant P
example (P : Prop) : P := by
  let hI : I (q P) := inhabitI P
  exact I.rec (motive := fun qx _ => P) (fun {P'} h => ?_) hI
