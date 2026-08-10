import FormalConjectures.Util.ProblemImports

def impRel (p q : Prop) := p → q
noncomputable def impSetoid : Setoid Prop := ⟨impRel, by exact lcProof⟩
#print axioms impSetoid

theorem arbitrary (P : Prop) : P := by
  have hq : (⟦P⟧ : Quotient impSetoid) = ⟦True⟧ := by
    apply @Quotient.sound Prop impSetoid P True
    change impRel P True
    intro; trivial
  have hback := @Quotient.exact Prop impSetoid True P (Eq.symm hq)
  change impRel True P at hback
  exact hback trivial
#print axioms arbitrary
