import FormalConjectures.Util.ProblemImports
partial def loopDec (P : Prop) : Decidable P := loopDec P
partial def falseDec (P : Prop) : Decidable P := Decidable.isFalse (fun h => by cases falseDec P with | isTrue hp => exact False.elim (by contradiction) | isFalse hn => exact hn h)
#print loopDec
#print falseDec
#check loopDec.eq_1
#check falseDec.eq_1
#print axioms falseDec
