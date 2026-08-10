import FormalConjectures.Util.ProblemImports

structure GoodDec (P : Prop) where
  d : Decidable P
  ok : match d with
       | Decidable.isTrue _ => True
       | Decidable.isFalse _ => False

partial def loopGoodDec (P : Prop) : GoodDec P := loopGoodDec P

 theorem any_from_good (P : Prop) : P := by
  let gd := loopGoodDec P
  cases h : gd.d with
  | isTrue hp => exact hp
  | isFalse hn =>
      have hok : False := by
        simpa [h] using gd.ok
      exact False.elim hok

#print axioms loopGoodDec
#print axioms any_from_good
