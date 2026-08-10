import FormalConjectures.Util.ProblemImports

#check Classical.choice
#check Classical.decEq
#check Classical.dec
#check Classical.em
#check Classical.propComplete
#check Classical.byContradiction
#check Classical.choice_of_true
#check Classical.ofNonempty
#check Classical.arbitrary
#print axioms Classical.propComplete
#print axioms Classical.em
#print axioms Classical.byContradiction

abbrev Target : Prop := ∀ n : ℕ, n > 0 → ∃ k : ℕ, Nat.Prime ((3 ^ n - k) * (2 ^ n) - 1) ∧ Nat.Prime ((3 ^ n - k) * (2 ^ n) + 1)

example : Target ∨ ¬ Target := Classical.em Target

example : Target := by
  classical
  by_cases h : Target
  · exact h
  · -- branch is exactly disproof, cannot close
    have hc := Classical.propComplete Target
    cases hc with
    | inl ht =>
        exact cast ht.symm True.intro
    | inr hf =>
        -- hf : Target = False
        fail_if_success exact cast hf.symm False.elim
        exact False.elim ?_
