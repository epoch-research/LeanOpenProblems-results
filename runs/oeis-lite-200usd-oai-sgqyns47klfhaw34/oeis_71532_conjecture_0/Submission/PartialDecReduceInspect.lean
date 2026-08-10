import FormalConjectures.Util.ProblemImports

partial def decLoop (P : Prop) : Decidable P := decLoop P
partial def decFalseAlways (P : Prop) : Decidable P := Decidable.isFalse (fun h => by cases decFalseAlways P with | isFalse hn => exact hn h | isTrue hp => exact False.elim (by exact decFalseAlways P |>.rec (fun hn => hn h) (fun hp => ?bad)))

#reduce decLoop True
#eval (match decLoop True with | isTrue _ => true | isFalse _ => false)
#print decLoop
