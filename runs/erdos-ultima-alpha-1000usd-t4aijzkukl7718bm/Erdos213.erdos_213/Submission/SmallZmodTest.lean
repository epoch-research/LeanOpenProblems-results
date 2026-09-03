import FormalConjecturesUtil
abbrev F := ZMod 101
example (j : F) : (102 : F)*j = j := by
 norm_num [F, ZMod.reduceNat]
example {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) : f (8 : R) = 8 := by
 norm_num
example (j : F) : (102 : F)*j = j := by
 have h : (102 : F) = 1 := by decide
 rw [h,one_mul]
