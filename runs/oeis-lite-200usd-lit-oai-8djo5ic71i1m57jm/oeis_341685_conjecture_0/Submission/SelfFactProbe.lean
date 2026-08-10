import FormalConjectures.Util.ProblemImports

noncomputable def xi_3_local : Padic 3 := tsum (fun k : ℕ => (Nat.factorial k : Padic 3))

instance factTarget : Fact (IsAlgebraic ℚ xi_3_local) where
  out := Fact.out

example : IsAlgebraic ℚ xi_3_local := Fact.out
#print axioms factTarget
