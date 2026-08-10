import FormalConjectures.Util.ProblemImports

namespace QuotOutRelationExplore

-- Relation r p q := p → q. EqvGen is equivalence closure, too weak (symmetric closure).
def relImp (p q : Prop) := p → q

def qImp (P : Prop) : Quot relImp := Quot.mk _ P

-- out is in the EqvGen class of P.
example (P : Prop) : Relation.EqvGen relImp (Quot.out (qImp P)) P := by
  have h := Quot.out_eq (qImp P)
  exact (Quot.eq).mp h

-- Can EqvGen relImp a b plus a imply b? likely false due symm.
example : Relation.EqvGen relImp True False := by
  -- quotient equality from Quot.sound (False -> True) reversed?
  apply Relation.EqvGen.symm
  exact Relation.EqvGen.rel (by intro h; cases h)

-- Relation r p q := q -> p, also no.
def relRevImp (p q : Prop) := q → p

def qRev (P : Prop) : Quot relRevImp := Quot.mk _ P
example (P : Prop) : Relation.EqvGen relRevImp (Quot.out (qRev P)) P := (Quot.eq).mp (Quot.out_eq (qRev P))

end QuotOutRelationExplore
