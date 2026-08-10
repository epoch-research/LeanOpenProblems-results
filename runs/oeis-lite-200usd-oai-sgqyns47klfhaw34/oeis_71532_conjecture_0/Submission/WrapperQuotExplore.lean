import FormalConjectures.Util.ProblemImports

namespace WrapperQuotExplore

-- A subtype of propositions equivalent to P. Nonempty iff P, so no.
def EqvProp (P : Prop) := {Q : Prop // Q ↔ P}

-- Quotient all propositions together. Inhabited, but can we define a projection respecting relation?
def AllQ := Quot (fun (_ _ : Prop) => True)

def qOf (P : Prop) : AllQ := Quot.mk _ P

-- Any Prop-valued function out of AllQ must be constant up to equality, requiring propext of all props.
-- Try instead return Sort: subtype of representatives? impossible.

-- A wrapper carrying a quotient plus an equality to qOf P. It is inhabited for all P since all quotients equal.
structure W (P : Prop) where
  q : AllQ
  eq : q = qOf P

instance (P : Prop) : Inhabited (W P) := ⟨⟨qOf True, Quot.sound trivial⟩⟩

-- Can we extract P from W P by quotient induction on q and eq?
theorem getP? (P : Prop) (w : W P) : P := by
  rcases w with ⟨q, hq⟩
  -- q = qOf P. quotient induction on q gives a representative R and equality qOf R = qOf P,
  -- exact gives EqvGen True R P (trivial), no implication.
  induction q using Quot.ind with
  | h R =>
    -- hq : qOf R = qOf P
    have eg := Quot.eqvGen_exact hq
    -- eg : Relation.EqvGen (fun _ _ => True) R P
    -- no way to get P.
    sorry

#print axioms W.instInhabited
#print axioms getP?

end WrapperQuotExplore
