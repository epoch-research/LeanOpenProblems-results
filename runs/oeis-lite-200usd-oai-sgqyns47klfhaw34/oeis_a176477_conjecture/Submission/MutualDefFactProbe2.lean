import FormalConjectures.Util.ProblemImports

mutual
  def bad (n : Nat) : True := by
    exact badFact.out n
  def badFact : Fact (∀ n : Nat, True) := ⟨fun n => bad n⟩
end
#check bad
#print axioms bad
