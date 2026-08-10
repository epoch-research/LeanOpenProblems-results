import FormalConjectures.Util.ProblemImports

mutual
  def bad (n : Nat) : True := by
    exact Fact.out (p := ∀ n : Nat, True) n
  def badFact : Fact (∀ n : Nat, True) := ⟨fun n => bad n⟩
end
#check bad
#print axioms bad
