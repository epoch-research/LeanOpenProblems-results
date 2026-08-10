import FormalConjectures.Util.ProblemImports

inductive MyQRel4 : Bool → Bool → Prop | mk : MyQRel4 a b
abbrev MyQ4 := Quot MyQRel4
abbrev myqt4 : MyQ4 := Quot.mk MyQRel4 true
abbrev myqf4 : MyQ4 := Quot.mk MyQRel4 false
inductive MyFam4 : MyQ4 → Type | intro : MyFam4 myqt4

def badElem4 : MyFam4 myqf4 := Eq.ndrec MyFam4.intro (show myqt4 = myqf4 from Quot.sound MyQRel4.mk)

def noFamFalse4 (x : MyFam4 myqf4) : False := nomatch x

theorem badFalse4 : False := noFamFalse4 badElem4
#print axioms badFalse4
