import FormalConjectures.Util.ProblemImports

inductive MyQRel : Bool → Bool → Prop | mk : MyQRel a b
abbrev MyQ := Quot MyQRel
abbrev myqt : MyQ := Quot.mk MyQRel true
abbrev myqf : MyQ := Quot.mk MyQRel false

inductive MyFam : MyQ → Type
| intro : MyFam myqt

example : myqt = myqf := Quot.sound MyQRel.mk

def badElem : MyFam myqf := Eq.ndrec MyFam.intro (show myqt = myqf from Quot.sound MyQRel.mk)

def noFamFalse (x : MyFam myqf) : False := by
  cases x

#print axioms badElem
#print axioms noFamFalse

theorem badFalse : False := noFamFalse badElem
#print axioms badFalse
