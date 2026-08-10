import FormalConjectures.Util.ProblemImports

def impRel (p q : Prop) := p → q

partial def impSetoid : Setoid Prop where
  r := impRel
  iseqv := {
    refl := fun p hp => hp
    symm := fun {p q} hpq => by
      have hrec : impSetoid.r p q := by
        change impRel p q
        exact hpq
      have hback : impSetoid.r q p := impSetoid.iseqv.symm hrec
      change impRel q p at hback
      exact hback
    trans := fun {p q r} hpq hqr hp => hqr (hpq hp)
  }

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
