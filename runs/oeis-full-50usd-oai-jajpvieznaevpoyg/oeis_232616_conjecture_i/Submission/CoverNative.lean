import FormalConjectures.Util.ProblemImports
set_option maxHeartbeats 0
set_option maxRecDepth 20000000
open Finset ZMod Nat Set Classical

def A232616_prop (n m : ℕ) [NeZero n] : Prop :=
  (univ : Finset (ZMod n)) = (Finset.Icc 1 m).image fun k ↦ (Nat.cast (2 ^ k - k) : ZMod n)

theorem cover_native : A232616_prop 550172 17135927 := by
  unfold A232616_prop
  native_decide
#print axioms cover_native
