import FormalConjectures.Util.ProblemImports
theorem T (n : Nat) : True := by
  have h := T (n+1)
  trivial
#print axioms T

theorem F (n : Nat) : False := by
  have h := F (n+1)
  exact h
#print axioms F
