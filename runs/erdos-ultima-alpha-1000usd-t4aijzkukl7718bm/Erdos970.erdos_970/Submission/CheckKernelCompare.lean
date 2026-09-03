import FormalConjecturesUtil
set_option maxRecDepth 10000
example : (1024 : ℕ) ≤ 65536 := by decide
example : (1024 : ℕ) ≤ 65536 := by norm_num
example : (1024 : ℕ) ≤ 65536 := by omega
