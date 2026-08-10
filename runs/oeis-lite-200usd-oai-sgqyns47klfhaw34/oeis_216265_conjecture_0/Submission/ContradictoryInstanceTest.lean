import FormalConjectures.Util.ProblemImports

instance : Infinite PUnit := ⟨by
  intro h
  cases h with
  | intro n e =>
    -- there is an equivalence for n=1, so should be impossible to prove False
    fail_if_success simp at e
    sorry⟩

theorem bad : False := Fintype.false (α := PUnit) inferInstance
#print axioms bad
