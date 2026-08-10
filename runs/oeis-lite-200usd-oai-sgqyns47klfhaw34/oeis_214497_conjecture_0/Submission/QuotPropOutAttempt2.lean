import FormalConjectures.Util.ProblemImports

-- Relation identifying True with an arbitrary proposition P.
def R (P : Prop) : Prop → Prop → Prop := fun A B => (A = True ∧ B = P) ∨ (A = P ∧ B = True)

example (P : Prop) : Quot (R P) := Quot.mk _ True

-- We can prove the quotient classes equal.
example (P : Prop) : Quot.mk (R P) True = Quot.mk (R P) P := Quot.sound (Or.inl ⟨rfl, rfl⟩)

-- Can Quot.out of that class be forced to be True and P simultaneously?
example (P : Prop) : P := by
  let q : Quot (R P) := Quot.mk _ True
  have hqT : Quot.mk (R P) (Quot.out q) = Quot.mk (R P) True := by
    simpa [q] using Quot.out_eq q
  have hqP : Quot.mk (R P) True = Quot.mk (R P) P := Quot.sound (Or.inl ⟨rfl, rfl⟩)
  -- Quot.eq only yields EqvGen, not the relation, and EqvGen may relate via transitive closure.
  have heqv : Relation.EqvGen (R P) (Quot.out q) P := (Quot.eq).mp (hqT.trans hqP)
  induction heqv with
  | rel x y h =>
      rcases h with h|h
      · simpa [h.1] using (show True from trivial)
      · -- if x=P, y=True; impossible? but x=out q, y=P in this branch? no
        subst y
        -- stuck
        sorry
  | refl x =>
      -- gives out q = P, no proof
      sorry
  | symm x y h ih =>
      sorry
  | trans x y z h1 h2 ih1 ih2 =>
      exact ih2
