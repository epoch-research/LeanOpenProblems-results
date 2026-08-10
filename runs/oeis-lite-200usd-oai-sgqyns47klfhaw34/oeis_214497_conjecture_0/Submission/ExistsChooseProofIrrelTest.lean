import FormalConjectures.Util.ProblemImports

#check Classical.choose
#check Exists.choose
#check Classical.choose_spec
#check Exists.choose_spec
#check Exists.choose_eq

example : (Exists.intro 0 True.intro : ∃ n : Nat, True) = Exists.intro 1 True.intro := proof_irrel _ _

example : False := by
  let h0 : ∃ n : Nat, True := ⟨0, True.intro⟩
  let h1 : ∃ n : Nat, True := ⟨1, True.intro⟩
  have heq : h0 = h1 := proof_irrel _ _
  have hc : Classical.choose h0 = Classical.choose h1 := congrArg Classical.choose heq
  -- cannot show choose h0 = 0 / choose h1 = 1
  exact?

example : False := by
  let h0 : ∃ n : Nat, n = 0 := ⟨0, rfl⟩
  let h1 : ∃ n : Nat, n = 1 := ⟨1, rfl⟩
  -- propositions differ, no proof_irrel equality
  exact?
