import FormalConjectures.Util.ProblemImports

abbrev Q := Quot (fun _ _ : Prop => True)
def q (P : Prop) : Q := Quot.mk _ P

inductive Holds : Q -> Prop where
| intro {P : Prop} : P -> Holds (q P)

noncomputable def holdsAny (P : Prop) : Holds (q P) := by
  exact Eq.mp (congrArg Holds (Quot.sound (r := fun _ _ : Prop => True) trivial : q True = q P)) (Holds.intro True.intro)

-- attempt eliminator into Quot.out q
noncomputable def extractOut (qq : Q) (h : Holds qq) : Quot.out qq := by
  -- induction on quotient into Prop allowed
  revert h
  refine Quot.ind (r := fun _ _ : Prop => True) (β := fun qq => Holds qq -> Quot.out qq) ?_ qq
  intro P hP
  -- hP : Holds (q P), target Quot.out(q P)
  -- try cases hP
  cases hP with
  | intro hp =>
    -- hp : R with equation qP=qR maybe blocked?
    exact ?_

example : False := extractOut (q False) (holdsAny False)
#print axioms holdsAny
#print axioms extractOut
