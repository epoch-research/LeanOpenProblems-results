import FormalConjecturesUtil
example (x : ZMod 9) : 11123733248919072*x = 0 := by
  rw [show (11123733248919072 : ZMod 9) = 0 by decide, zero_mul]
example (x : ZMod 9) : 11123733248919072*x = 0 := by
  simp only [show (11123733248919072 : ZMod 9) = 0 by decide, zero_mul]
example (x : ZMod 9) : 11123733248919072*x = 0 := by
  norm_num [ZMod, Fin.ofNat, Fin.modNat, OfNat.ofNat]
