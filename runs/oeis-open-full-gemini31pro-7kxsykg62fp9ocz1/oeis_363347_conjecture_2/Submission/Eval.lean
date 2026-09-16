import Submission.Spec
open Rat Nat

theorem A363347_6 : A363347 6 = 11 := by
  rw [A363347]
  norm_num
  rw [continued_fraction_denominator]; norm_num
  rw [continued_fraction_denominator]; norm_num
  rw [continued_fraction_denominator]; norm_num
  rw [continued_fraction_denominator]; norm_num
  rw [continued_fraction_denominator]; norm_num
