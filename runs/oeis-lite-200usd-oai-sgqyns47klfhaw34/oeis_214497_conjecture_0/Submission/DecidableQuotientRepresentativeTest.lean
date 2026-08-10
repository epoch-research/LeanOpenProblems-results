import FormalConjectures.Util.ProblemImports

-- Relation on Decidable P: different constructors imply P; same constructors are True.
inductive DecRel (P : Prop) : Decidable P → Decidable P → Prop where
| sameTrue (h1 h2 : P) : DecRel P (.isTrue h1) (.isTrue h2)
| sameFalse (h1 h2 : ¬ P) : DecRel P (.isFalse h1) (.isFalse h2)
| tf (h : P) (hn : ¬ P) : DecRel P (.isTrue h) (.isFalse hn)
| ft (hn : ¬ P) (h : P) : DecRel P (.isFalse hn) (.isTrue h)

example (P : Prop) : P := by
  let d : Decidable P := Classical.choice (Classical.instNonemptyDecidable P)
  let q : Quot (DecRel P) := Quot.mk (DecRel P) d
  have hmkout : Relation.EqvGen (DecRel P) q.out d := Quot.mk_out q
  cases d with
  | isTrue hp => exact hp
  | isFalse hn =>
    -- Need extract P from EqvGen between q.out and false representative.
    cases q.out with
    | isTrue hp => exact hp
    | isFalse hn2 =>
      induction hmkout with
      | rel r => cases r <;> assumption
      | refl => exact False.elim (hn ?needP)
      | symm _ ih => exact ih
      | trans _ _ ih1 ih2 => exact ih2
