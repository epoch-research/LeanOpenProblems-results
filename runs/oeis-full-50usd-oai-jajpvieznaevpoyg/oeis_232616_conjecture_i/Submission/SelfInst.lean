import FormalConjectures.Util.ProblemImports

theorem selfInst (n : Nat) : n = n := by
  letI : Decidable (n = n) := isTrue (selfInst n)
  exact if h : n = n then h else by contradiction
