import FormalConjecturesUtil
#check map_ofNat
#check map_natCast
#check map_one
example {F : Type*} [Field F] (φ : ZMod 7 →+* F) : φ 2 = 2 := by
  have h : (2 : ZMod 7) = 1+1 := by decide
  rw [h,map_add,map_one]
  norm_num
example {F : Type*} [Field F] (φ : ZMod 7 →+* F) : φ 2 = 2 := by
  exact map_ofNat φ 2
