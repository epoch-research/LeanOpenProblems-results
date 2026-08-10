import FormalConjectures.Util.ProblemImports
set_option maxHeartbeats 0
set_option maxRecDepth 10000000
open Finset ZMod Nat Set

def A232616_prop (n m : ℕ) [NeZero n] : Prop :=
  (univ : Finset (ZMod n)) = (Finset.Icc 1 m).image fun k ↦ (Nat.cast (2 ^ k - k) : ZMod n)

example : ¬ A232616_prop 550172 16331503 := by
  unfold A232616_prop
  native_decide

-- example : A232616_prop 550172 17135927 := by
--  unfold A232616_prop
--  native_decide
