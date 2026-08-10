import FormalConjectures.Util.ProblemImports

#check Nat.sInf
#check Nat.sInf_mem
#check Nat.sInf_le
#check Nat.le_sInf
#check csInf_mem
#check sInf_mem
#check WellFoundedLT.has_min

example (s : Set ℕ) : s (sInf s) := by
  exact Nat.sInf_mem s
