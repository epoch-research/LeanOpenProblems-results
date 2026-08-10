import FormalConjectures.Util.ProblemImports
set_option diagnostics true
open Finset ZMod Nat Set

def A232616_prop (n m : ℕ) [NeZero n] : Prop :=
  (univ : Finset (ZMod n)) = (Finset.Icc 1 m).image fun k ↦ (Nat.cast (2 ^ k - k) : ZMod n)

#synth Decidable (A232616_prop 1 1)
#synth DecidableEq (ZMod 1)
#synth Decidable ((univ : Finset (ZMod 1)) = (Finset.Icc 1 1).image fun k ↦ (Nat.cast (2 ^ k - k) : ZMod 1))
#synth Decidable (@A232616_prop 1 1 (by infer_instance))
example : @A232616_prop 1 1 (by infer_instance) := by native_decide

