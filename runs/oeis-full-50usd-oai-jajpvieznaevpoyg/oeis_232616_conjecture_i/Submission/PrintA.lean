import FormalConjectures.Util.ProblemImports
open Finset ZMod Nat Set Classical

def A232616_prop (n m : ℕ) [NeZero n] : Prop :=
  (univ : Finset (ZMod n)) = (Finset.Icc 1 m).image fun k ↦ (Nat.cast (2 ^ k - k) : ZMod n)

noncomputable def A232616 (n : ℕ) : ℕ :=
  if h : n = 0 then 0
  else
    have hn : NeZero n := NeZero.mk h
    let S : Set ℕ := { m : ℕ | A232616_prop n m }
    sInf S

#print A232616
set_option pp.all true in
#print A232616

#print A232616_prop
