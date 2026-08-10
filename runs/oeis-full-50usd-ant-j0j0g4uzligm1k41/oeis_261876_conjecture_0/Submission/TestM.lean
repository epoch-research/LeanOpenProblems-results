import FormalConjectures.Util.ProblemImports
set_option maxHeartbeats 0
-- specialized: count i in [lo,lo+len) with i%7==0, log-depth
def cntSpec : Nat → Nat → Nat → Nat
  | 0, _, _ => 0
  | _, _, 0 => 0
  | _, lo, 1 => if lo % 7 == 0 then 1 else 0
  | (fuel+1), lo, len =>
      let h := len / 2
      cntSpec fuel lo h + cntSpec fuel (lo+h) (len-h)
example : cntSpec 40 0 100000 = 14286 := by rfl
