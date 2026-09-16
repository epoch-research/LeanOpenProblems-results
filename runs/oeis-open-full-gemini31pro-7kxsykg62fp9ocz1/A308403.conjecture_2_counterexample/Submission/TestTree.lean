import Mathlib

def treeSum (start len : Nat) : Nat :=
  if len = 0 then 0
  else if len = 1 then 1
  else
    let half := len / 2
    treeSum start half + treeSum (start + half) (len - half)

set_option maxRecDepth 2000000

theorem test : treeSum 0 4000000 = 4000000 := by decide
