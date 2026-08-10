import FormalConjectures.Util.ProblemImports

inductive MyQRel2 : Bool → Bool → Prop | mk : MyQRel2 a b
abbrev MyQ2 := Quot MyQRel2
abbrev myqt2 : MyQ2 := Quot.mk MyQRel2 true
abbrev myqf2 : MyQ2 := Quot.mk MyQRel2 false

inductive MyFam2 : MyQ2 → Type
| intro : MyFam2 myqt2

def badElem2 : MyFam2 myqf2 := Eq.ndrec MyFam2.intro (show myqt2 = myqf2 from Quot.sound MyQRel2.mk)

example (x : MyFam2 myqf2) : False := by
  have hq : myqf2 = myqt2 := Quot.sound MyQRel2.mk
  -- try substituting index?
  -- rw [hq] at x
  cases x
