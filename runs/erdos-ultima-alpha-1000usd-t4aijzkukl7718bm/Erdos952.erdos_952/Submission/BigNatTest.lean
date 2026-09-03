import FormalConjecturesUtil
/-! Check kernel evaluation of large bit masks. -/
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
example : (((1 : ℕ) <<< 672945) - 1) >>> 29 = ((1 : ℕ) <<< (672945 - 29)) - 1 := by
  decide +kernel
example : let q := (((1 : ℕ) <<< 672945) - 1) / (((1 : ℕ) <<< 29) - 1)
  q * (((1 : ℕ) <<< 29) - 1) = ((1 : ℕ) <<< 672945) - 1 := by
  decide +kernel
