import Submission.DoubleVaughan
open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta
open Erdos972Vaughan Erdos972DoubleVaughan
example : typeIIPart 3 3 30 = Real.log 5 := by
  norm_num [typeIIPart, ArithmeticFunction.mul_apply, tail, cutoff, Erdos972Vaughan.sub_apply, Nat.divisorsAntidiagonal, Nat.divisors]
#print ArithmeticFunction.vonMangoldt
#check ArithmeticFunction.mul_apply_mul
#check ArithmeticFunction.mul_apply
#check ArithmeticFunction.vonMangoldt_apply
