import Submission.RelativeChang
open scoped Classical
#check mul_div_mul_right
#check mul_div_mul_right'
#check mul_div_mul_right_eq_div
#check mul_div_mul_right₀
#check div_mul_cancel_right
#check mul_div_mul_right
#check div_eq_mul_inv
#check inv_mul_cancel_right
example {G : Type*} [AddCommGroup G] (a b c : AddChar G ℂ) :
    a*c/(b*c)=a/b := by
  simp only [div_eq_mul_inv, mul_inv_rev, mul_assoc, mul_inv_cancel_left]
