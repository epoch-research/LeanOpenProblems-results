import Submission.ArithmeticProgressionObstruction
#check map_ofNat
#check map_natCast
#check RingHom.map_ofNat
#check Int.cast_ne_zero
#check Int.castRingHom_apply
#check RingHom.map_one
#check map_add
example {R S : Type*} [Ring R] [Ring S] (f : R →+* S) : f 2 = 2 := by
  change f (1 + 1) = (1 + 1)
  simp
