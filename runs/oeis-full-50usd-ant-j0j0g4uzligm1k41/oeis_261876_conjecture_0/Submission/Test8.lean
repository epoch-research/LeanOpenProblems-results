import FormalConjectures.Util.ProblemImports
set_option maxHeartbeats 0
def treeCount (f : Nat → Bool) : Nat → Nat → Nat → Nat
  | 0, _, _ => 0
  | _, _, 0 => 0
  | _, lo, (Nat.succ 0) => if f lo then 1 else 0
  | (fuel+1), lo, len =>
      let h := len / 2
      treeCount f fuel lo h + treeCount f fuel (lo+h) (len-h)
-- count i in [0,10^6) with i%7==0  -> ceil(10^6/7)=142858
example : treeCount (fun i => i % 7 == 0) 40 0 1000000 = 142858 := by rfl
