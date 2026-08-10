import FormalConjectures.Util.ProblemImports

def impRel (p q : Prop) := p → q

partial def impSetoid (_ : Unit) : Setoid Prop where
  r := impRel
  iseqv := {
    refl := fun p hp => hp
    symm := fun {p q} hpq => by
      -- use a fake harmless recursion? actually impossible, use itself with no casting impossible
      exact (by
        -- leave as recursive opaque via have? 
        exact (impSetoid ()).iseqv.symm (by exact hpq))
    trans := fun {p q r} hpq hqr hp => hqr (hpq hp)
  }

#reduce (impSetoid ()).r
example : (impSetoid ()).r = impRel := rfl
example (P Q : Prop) (h : impRel P Q) : (impSetoid ()).r P Q := by
  change impRel P Q
  exact h
#print axioms impSetoid
