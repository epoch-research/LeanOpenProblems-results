import FormalConjectures.Util.ProblemImports
open Finset ZMod Nat Set Classical

def A232616_prop (n m : ℕ) [NeZero n] : Prop :=
  (univ : Finset (ZMod n)) = (Finset.Icc 1 m).image fun k ↦ (Nat.cast (2 ^ k - k) : ZMod n)

example : A232616_prop 1 1 := by decide
example : A232616_prop 2 2 := by decide
example : ¬ A232616_prop 29 194 := by decide
example : A232616_prop 29 195 := by decide
