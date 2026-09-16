import Submission.Spec
open Nat Rat Finset

theorem a2000 : A309391 2000 = 1 := by
  change Nat.gcd 2000 ((harmonic_number 1998).num - ↑(harmonic_number 1998).den).natAbs = 1
  unfold harmonic_number
  norm_num
