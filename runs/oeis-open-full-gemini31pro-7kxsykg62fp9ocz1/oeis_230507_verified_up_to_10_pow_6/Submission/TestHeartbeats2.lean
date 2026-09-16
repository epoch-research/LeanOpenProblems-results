set_option maxHeartbeats 0

def treeSum : Nat → Nat → Nat → Nat
| 0, start, len => 0
| fuel + 1, start, len =>
  if len = 0 then 0
  else if len = 1 then start
  else
    let half := len / 2
    treeSum fuel start half + treeSum fuel (start + half) (len - half)

theorem t1 : treeSum 30 0 100000 = 4999950000 := by decide
