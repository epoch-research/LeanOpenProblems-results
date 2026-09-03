import Submission.AveragedLocalCircleCounting
open scoped Classical
variable {G : Type*} [AddCommGroup G] [Fintype G]
#synth CommGroup (AddChar G ℂ)
#check div_eq_iff_mul_eq
#check div_eq_iff
#check mul_div_cancel_left
#check AddChar.div_apply
#check Complex.norm_sub_sq
#check Complex.normSq_sub
#check Complex.sq_norm
#check AddChar.inv_apply
