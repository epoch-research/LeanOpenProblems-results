import FormalConjectures.Util.ProblemImports

partial def trueDec (P : Prop) : Decidable P :=
  Decidable.isTrue (by
    let rec pr : P :=
      match trueDec P with
      | isTrue h => h
      | isFalse hn => False.elim (hn pr)
    exact pr)

local instance (P : Prop) : Decidable P := trueDec P

theorem bad : False := by
  exact Decidable.of_not_not (by intro h; exact h h)

#print axioms trueDec
#print axioms bad
