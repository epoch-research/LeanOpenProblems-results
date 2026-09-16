import Submission.Spec
open Nat Rat Finset

theorem a8 : A309391 8 = 1 := by
  change Nat.gcd 8 ((harmonic_number 6).num - ↑(harmonic_number 6).den).natAbs = 1
  unfold harmonic_number
  norm_num
