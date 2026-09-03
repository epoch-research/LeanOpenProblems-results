import FormalConjecturesUtil
/-! Scratch. -/
open scoped CharTwo
variable {E : Type*} [Field E] [CharP E 2]
#check CharP.cast_eq_zero
#check CharTwo.two_eq_zero
#check CharP.cast_eq_zero E 2
example (x y : E) : x*y*2=0 := by
  have h2 : (2:E)=0 := CharP.cast_eq_zero E 2
  rw [h2,mul_zero]
example (x y : E) : (x+y)*(x+y+1)=x^2+x+y^2+y := by
  have h2 : (2:E)=0 := CharP.cast_eq_zero E 2
  ring_nf
  simp only [h2,mul_zero,add_zero]
  ring
