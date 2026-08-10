import FormalConjectures.Util.ProblemImports

theorem arbitrary (P : Prop) : P := by
  let rec d : Decidable P := Decidable.isTrue hp
  and hp : P := by
    cases d with
    | isTrue h => exact h
    | isFalse hn => exact False.elim (hn hp)
  exact hp

#print axioms arbitrary
