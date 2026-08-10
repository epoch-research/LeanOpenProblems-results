import FormalConjectures.Util.ProblemImports

partial def d (P : Prop) : Decidable P :=
  Decidable.isTrue (@Decidable.byContradiction P (d P) (fun hn => by
    cases hd : d P with
    | isTrue hp => exact hn hp
    | isFalse hn2 =>
        -- Need contradiction from hn and hn2. Try constructor tag equality from proof irrelevance.
        have e : (d P) = Decidable.isFalse hn := Subsingleton.elim _ _
        rw [hd] at e
        -- e : isFalse hn2 = isFalse hn, no contradiction
        exact ?_))

theorem arbitrary (P : Prop) : P := by
  haveI := d P
  exact @Decidable.byContradiction P (d P) (fun hn => by
    cases hd : d P with
    | isTrue hp => exact hn hp
    | isFalse hn2 => exact ?_)

#print axioms d
#print axioms arbitrary
