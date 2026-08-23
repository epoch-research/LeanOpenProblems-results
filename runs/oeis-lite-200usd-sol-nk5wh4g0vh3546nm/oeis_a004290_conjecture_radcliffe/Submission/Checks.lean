import FormalConjectures.Util.ProblemImports
#check Nat.ofDigits_append
#check Nat.ofDigits_replicate
#check Nat.ofDigits_cons
#check Nat.ofDigits_zero_cons
#check Nat.ofDigits_singleton
#check List.mem_append
#reduce Nat.ofDigits 10 ([0,0,1])
example (k : ℕ) : Nat.ofDigits 10 (List.replicate k 0 ++ [1]) = 10^k := by
  induction k with
  | zero => simp [Nat.ofDigits]
  | succ k ih => simp [List.replicate_succ, Nat.ofDigits, ih, pow_succ]
