import FormalConjectures.Util.ProblemImports

def impRel (p q : Prop) := p → q

partial def impSetoid (_ : Unit) : Setoid Prop where
  r := impRel
  iseqv := by
    let rec eqv (_ : Unit) : Equivalence impRel := {
      refl := fun p hp => hp
      symm := fun {p q} hpq => (eqv ()).symm hpq
      trans := fun {p q r} hpq hqr hp => hqr (hpq hp)
    }
    exact eqv ()

example : (impSetoid ()).r = impRel := rfl

theorem arbitrary (P : Prop) : P := by
  have hq : (⟦P⟧ : Quotient (impSetoid ())) = ⟦True⟧ := by
    apply @Quotient.sound Prop (impSetoid ()) P True
    change impRel P True
    intro; trivial
  have hback := @Quotient.exact Prop (impSetoid ()) True P (Eq.symm hq)
  change impRel True P at hback
  exact hback trivial

#print axioms impSetoid
#print axioms arbitrary
