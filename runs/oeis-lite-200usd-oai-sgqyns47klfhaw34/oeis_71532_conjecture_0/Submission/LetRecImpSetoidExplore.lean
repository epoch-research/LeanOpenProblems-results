import FormalConjectures.Util.ProblemImports

def impRel (p q : Prop) := p → q

noncomputable def impSetoid : Setoid Prop := by
  let rec S : Setoid Prop := {
    r := impRel
    iseqv := {
      refl := fun p hp => hp
      symm := fun {p q} hpq => by
        intro hq
        have hqeq : (⟦q⟧ : Quotient S) = ⟦p⟧ := Eq.symm (@Quotient.sound Prop S p q (by change impRel p q; exact hpq))
        have hback := @Quotient.exact Prop S q p hqeq
        change impRel q p at hback
        exact hback hq
      trans := fun {p q r} hpq hqr hp => hqr (hpq hp)
    }
  }
  exact S

theorem arbitrary (P : Prop) : P := by
  have hq : (⟦P⟧ : Quotient impSetoid) = ⟦True⟧ := by
    apply @Quotient.sound Prop impSetoid P True
    change impRel P True
    intro; trivial
  have hback := @Quotient.exact Prop impSetoid True P (Eq.symm hq)
  change impRel True P at hback
  exact hback trivial

#print axioms impSetoid
#print axioms arbitrary
