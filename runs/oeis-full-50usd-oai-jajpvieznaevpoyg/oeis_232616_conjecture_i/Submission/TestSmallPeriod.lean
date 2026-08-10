import FormalConjectures.Util.ProblemImports
set_option maxHeartbeats 0
set_option exponentiation.threshold 300

example : 2^147 ≡ 1 [MOD 343] := by native_decide
example : 2^147 ≡ 1 [MOD 343] := by norm_num [Nat.ModEq]
example : 2^200 ≡ 1 [MOD 401] := by norm_num [Nat.ModEq]
example : Nat.Coprime 343 401 := by norm_num
