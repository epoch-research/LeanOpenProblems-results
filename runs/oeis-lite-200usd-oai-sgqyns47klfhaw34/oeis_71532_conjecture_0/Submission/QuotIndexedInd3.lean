import FormalConjectures.Util.ProblemImports

inductive MyQRel3 : Bool → Bool → Prop | mk : MyQRel3 a b
abbrev MyQ3 := Quot MyQRel3
abbrev myqt3 : MyQ3 := Quot.mk MyQRel3 true
abbrev myqf3 : MyQ3 := Quot.mk MyQRel3 false

inductive MyFam3 : MyQ3 → Type
| intro : MyFam3 myqt3

example (x : MyFam3 myqf3) : True := by
  have hq : myqf3 = myqt3 := Quot.sound MyQRel3.mk
  rw [hq] at x
  cases x
  trivial
