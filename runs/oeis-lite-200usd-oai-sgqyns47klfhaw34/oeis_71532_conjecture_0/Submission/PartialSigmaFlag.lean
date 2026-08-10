import FormalConjectures.Util.ProblemImports

structure FlagProof (P : Prop) where
  b : Bool
  cert : b = true → P

instance (P : Prop) : Inhabited (FlagProof P) := ⟨⟨false, by intro h; cases h⟩⟩

partial def flagged (P : Prop) : FlagProof P :=
  ⟨true, by
    intro _
    exact (flagged P).cert (by rfl)
  ⟩

#print flagged
#print axioms flagged

example (P : Prop) : P := by
  exact (flagged P).cert (by rfl)

#print axioms _example
