import FormalConjectures.Util.ProblemImports

open Nat

def S214 (n : ℕ) : Set ℕ := {k : ℕ | Nat.Prime ((3 ^ n - k) * (2 ^ n) - 1) ∧ Nat.Prime ((3 ^ n - k) * (2 ^ n) + 1)}

#check Nat.sInf_def
#check Nat.sInf_mem
#check Nat.find_eq_iff
#check csInf_mem
#check isLeast_csInf
#check Set.Nonempty.csInf_mem
#check Set.Finite.min'
#check WellFounded.has_min

example (n : ℕ) : (sInf (S214 n)) ∈ S214 n := by
  exact?
