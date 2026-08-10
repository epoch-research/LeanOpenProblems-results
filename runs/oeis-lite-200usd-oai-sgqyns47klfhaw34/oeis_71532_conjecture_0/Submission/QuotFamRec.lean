import FormalConjectures.Util.ProblemImports
inductive MyQRel5 : Bool → Bool → Prop | mk : MyQRel5 a b
abbrev MyQ5 := Quot MyQRel5
abbrev myqt5 : MyQ5 := Quot.mk MyQRel5 true
abbrev myqf5 : MyQ5 := Quot.mk MyQRel5 false
inductive MyFam5 : MyQ5 → Type | intro : MyFam5 myqt5
#check MyFam5.rec
#check MyFam5.casesOn
#check MyFam5.noConfusion
