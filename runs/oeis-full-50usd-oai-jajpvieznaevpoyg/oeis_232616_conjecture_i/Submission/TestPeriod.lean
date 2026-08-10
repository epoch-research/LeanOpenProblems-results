import FormalConjectures.Util.ProblemImports
set_option maxHeartbeats 0
set_option exponentiation.threshold 40000

example : (2 : ZMod 137543) ^ 29400 = 1 := by norm_num
example : Nat.Coprime 150 2807 := by norm_num
example : (150 * 131) % 2807 = 1 := by norm_num
example : (550172 : Nat) = 196 * 2807 := by norm_num
example : (29400 : Nat) = 196 * 150 := by norm_num
