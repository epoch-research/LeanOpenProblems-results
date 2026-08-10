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

#check Nat.sInf_def
#check Nat.sInf_eq_zero
#check Nat.sInf_mem
#check Nat.sInf_le
#check csInf_le
#check Nat.find
#check Nat.nth
#check Nat.nth_mem
#check Nat.nth_le_nth
#check Nat.Prime
#check Nat.prime_two
#check Nat.nth_pos
#check Nat.nth_prime
#check Nat.nth_lt_nth

example (n : ℕ) (hn : 0 < n) : 0 < 2 * (Nat.nth Nat.Prime (n - 1) - 1) := by
  sorry

example (n : ℕ) : A232616 (n+1) < 2 * (Nat.nth Nat.Prime n - 1) := by
  simp [A232616]

