import FormalConjectures.Util.ProblemImports

#check Fact
#print Fact
#synth Fact True
#synth Fact False
#synth Fact (Nat.Prime 4)

example (P : Prop) [Fact P] : P := Fact.out

example (n : ℕ) (hn : n > 0) :
    ∃ k : ℕ, Nat.Prime ((3 ^ n - k) * (2 ^ n) - 1) ∧ Nat.Prime ((3 ^ n - k) * (2 ^ n) + 1) := by
  let k := 0
  refine ⟨k, ?_, ?_⟩
  · exact Fact.out
  · exact Fact.out
