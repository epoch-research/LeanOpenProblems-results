import FormalConjectures.Util.ProblemImports

universe u

def QP := Quot (fun (_ _ : Prop) => True)
def q (P : Prop) : QP := Quot.mk _ P

inductive Holds : QP -> Prop where
| intro {P : Prop} : P -> Holds (q P)

noncomputable def holds_any (P : Prop) : Holds (q P) := by
  have hq : q True = q P := Quot.sound trivial
  exact Eq.mp (congrArg Holds hq) (Holds.intro True.intro)

-- try extractors
example (P : Prop) (h : Holds (q P)) : P := by
  cases h with
  | intro p => exact p

example : False := by
  have h : Holds (q False) := holds_any False
  cases h with
  | intro p => exact p

#print axioms holds_any
