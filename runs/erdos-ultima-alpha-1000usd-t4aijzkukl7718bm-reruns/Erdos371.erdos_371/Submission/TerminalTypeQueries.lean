import FormalConjecturesUtil
import Submission.EuclideanCompression
#check Nat.cast_div_le
#print Nat.cast_div_le
set_option pp.all true in
#check Nat.cast_div_le (α := ℝ) (m := (3 : ℕ)) (n := (2 : ℕ)^2 * 5)
set_option pp.all true in
example (n : ℕ) (h : ¬ 0 < (n / 3 : ℕ)) : n / 3 = 0 := by omega
