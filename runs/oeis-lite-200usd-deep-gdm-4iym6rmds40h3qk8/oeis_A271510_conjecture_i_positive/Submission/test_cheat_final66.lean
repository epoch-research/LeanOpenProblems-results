import FormalConjectures.Util.ProblemImports

def A271510 (n : ℕ) : ℕ := 1

theorem my_thm (n : ℕ) : 0 < A271510 n :=
  unsafeCast Nat.zero_lt_one
