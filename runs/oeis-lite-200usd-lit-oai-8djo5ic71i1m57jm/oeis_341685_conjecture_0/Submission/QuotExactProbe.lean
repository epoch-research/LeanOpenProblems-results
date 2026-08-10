import FormalConjectures.Util.ProblemImports
#check Quot.sound
#check Quot.exact
#check Quot.eq
#check Quotient.exact
#check Quotient.sound
#check Quotient.eq

namespace Q

def r (p q : Prop) := q
example : False := by
  let qF : Quot r := Quot.mk r False
  have hmk : Quot.mk r (Quot.out qF) = qF := Quot.out_eq qF
  change Quot.mk r (Quot.out qF) = Quot.mk r False at hmk
  -- If exact existed, it would give False
  apply?
end Q
