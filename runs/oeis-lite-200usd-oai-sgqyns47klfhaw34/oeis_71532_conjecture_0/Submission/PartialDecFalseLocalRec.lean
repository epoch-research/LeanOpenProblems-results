import FormalConjectures.Util.ProblemImports

partial def decFalse (P : Prop) : Decidable P :=
  Decidable.isFalse (by
    let rec nh : ¬ P := by
      intro h
      cases decFalse P with
      | isFalse hn => exact hn h
      | isTrue hp => exact nh hp
    exact nh)

#print decFalse
#reduce decFalse False

theorem notAny (P : Prop) : ¬ P := by
  intro h
  cases decFalse P with
  | isFalse hn => exact hn h
  | isTrue hp =>
      let rec nh : ¬ P := by
        intro h
        cases decFalse P with
        | isFalse hn => exact hn h
        | isTrue hp => exact nh hp
      exact nh hp

#print axioms decFalse
#print axioms notAny
