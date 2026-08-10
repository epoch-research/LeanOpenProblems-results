import FormalConjectures.Util.ProblemImports
def treeSum (f : Nat → Nat) : Nat → Nat → Nat → Nat
  | 0, _, _ => 0
  | _, _, 0 => 0
  | _, lo, 1 => f lo
  | (fuel+1), lo, len =>
      let h := len / 2
      treeSum f fuel lo h + treeSum f fuel (lo+h) (len-h)
set_option maxHeartbeats 0 in
example : treeSum (fun _ => 1) 40 0 1000000 = 1000000 := by rfl
