import FormalConjectures.Util.ProblemImports

mutual
  theorem bad (n : Nat) : True := by
    exact Fact.out (p := ∀ n : Nat, True) n
  instance badFact : Fact (∀ n : Nat, True) := ⟨fun n => bad n⟩
end
#check bad
#print axioms bad
