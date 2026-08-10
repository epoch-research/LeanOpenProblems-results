import FormalConjectures.Util.ProblemImports

inductive DecRel (P : Prop) : Decidable P → Decidable P → Prop where
| sameTrue (h1 h2 : P) : DecRel P (.isTrue h1) (.isTrue h2)
| sameFalse (h1 h2 : ¬ P) : DecRel P (.isFalse h1) (.isFalse h2)
| tf (h : P) (hn : ¬ P) : DecRel P (.isTrue h) (.isFalse hn)
| ft (hn : ¬ P) (h : P) : DecRel P (.isFalse hn) (.isTrue h)

example (P : Prop) : Relation.EqvGen (DecRel P)
    (Quot.out (Quot.mk (DecRel P) (Classical.choice (Classical.instNonemptyDecidable P))))
    (Classical.choice (Classical.instNonemptyDecidable P)) := by
  let d : Decidable P := Classical.choice (Classical.instNonemptyDecidable P)
  let q : Quot (DecRel P) := Quot.mk (DecRel P) d
  have hq : Quot.mk (DecRel P) q.out = Quot.mk (DecRel P) d := by
    calc Quot.mk (DecRel P) q.out = q := Quot.out_eq q
      _ = Quot.mk (DecRel P) d := rfl
  exact Quot.eq.mp hq

example (P : Prop) : P := by
  let d : Decidable P := Classical.choice (Classical.instNonemptyDecidable P)
  let q : Quot (DecRel P) := Quot.mk (DecRel P) d
  have hq : Quot.mk (DecRel P) q.out = Quot.mk (DecRel P) d := by
    calc Quot.mk (DecRel P) q.out = q := Quot.out_eq q
      _ = Quot.mk (DecRel P) d := rfl
  have heqv : Relation.EqvGen (DecRel P) q.out d := Quot.eq.mp hq
  cases d with
  | isTrue hp => exact hp
  | isFalse hn =>
    -- Even with the EqvGen, the refl case blocks extraction.
    induction heqv with
    | rel r => cases r with
      | sameTrue h1 h2 => exact h1
      | sameFalse h1 h2 => exact False.elim (h1 ?missing)
      | tf h _ => exact h
      | ft _ h => exact h
    | refl => exact False.elim (hn ?missing2)
    | symm _ ih => exact ih
    | trans _ _ ih1 ih2 => exact ih2
