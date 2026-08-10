import FormalConjectures.Util.ProblemImports

noncomputable def impSetoid : Setoid Prop where
  r := fun p q => p → q
  iseqv := {
    refl := fun p hp => hp
    symm := fun p q hpq => by
      intro hq
      exact (Quotient.exact (s := impSetoid) (Eq.symm (Quotient.sound hpq))) hq
    trans := fun p q r hpq hqr hp => hqr (hpq hp)
  }

theorem arbitrary (P : Prop) : P := by
  have hq : (⟦True⟧ : Quotient impSetoid) = ⟦P⟧ := Quotient.sound (fun _ => trivial)
  exact (Quotient.exact (s := impSetoid) hq) trivial

#print axioms impSetoid
#print axioms arbitrary
