import Submission.JumpProfileTransfer
open MeasureTheory
#check intervalIntegral.integral_eq_sub_of_hasDerivAt
#check intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
#check HasDerivAt.mul
#check HasDerivAt.const_mul
#check HasDerivAt.add
#check HasDerivAt.sub
#check HasDerivAt.pow
#check hasDerivAt_const
#check Continuous.intervalIntegrable
#check intervalIntegral.integral_mono_on
#check intervalIntegral.integral_const
#check intervalIntegral.integral_add
#check intervalIntegral.integral_neg
#check Set.uIcc_subset_uIcc
#check Real.norm_eq_abs
#check abs_add_le
#check abs_mul
#check abs_sub
#check abs_sub_le
#check Real.rpow_le_rpow
example (a b c d x : ℝ) : HasDerivAt (fun t => a + b*t+c*t^2+d*t^3) (b+2*c*x+3*d*x^2) x := by
  convert (((hasDerivAt_const x a).add ((hasDerivAt_id x).const_mul b)).add
    (((hasDerivAt_id x).pow 2).const_mul c)).add
    (((hasDerivAt_id x).pow 3).const_mul d) using 1 <;> ring
