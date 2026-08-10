import FormalConjectures.Util.ProblemImports

noncomputable def impSetoid : Setoid Prop where
  r := fun (p q : Prop) => p → q
  iseqv := {
    refl := fun p hp => hp
    symm := fun {p q} hpq => by
      intro hq
      exact (@Quotient.exact Prop impSetoid q p (Eq.symm (@Quotient.sound Prop impSetoid p q hpq))) hq
    trans := fun {p q r} hpq hqr hp => hqr (hpq hp)
  }

theorem arbitrary (P : Prop) : P := by
  have hq : (⟦P⟧ : Quotient impSetoid) = ⟦True⟧ := @Quotient.sound Prop impSetoid P True (fun _ => trivial)
  exact (@Quotient.exact Prop impSetoid True P (Eq.symm hq)) trivial

#print axioms impSetoid
#print axioms arbitrary
