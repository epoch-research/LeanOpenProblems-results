import FormalConjectures.Util.ProblemImports

mutual
partial def dTrue (P : Prop) : Decidable P :=
  Decidable.isTrue (by
    -- If dFalse P is definitionally/reflection-wise false, its equality to dTrue is contradictory.
    have e : dTrue P = dFalse P := Subsingleton.elim _ _
    cases hdf : dFalse P with
    | isTrue hp => exact hp
    | isFalse hn =>
        -- rewrite e along hdf to get isTrue ? = isFalse hn? maybe cases e
        have : False := by
          -- substitute hdf into e
          rw [hdf] at e
          -- e : dTrue P = isFalse hn; split dTrue
          cases hdt : dTrue P with
          | isTrue hp =>
              rw [hdt] at e
              cases e
          | isFalse hn2 =>
              exact hn2 (False.elim (by
                rw [hdt] at e
                -- e is equality of two isFalse, no false
                exact hn (by
                  -- circular fallback from dTrue
                  cases dTrue P with
                  | isTrue hp => exact hp
                  | isFalse hn3 => exact False.elim (hn3 (by exact hp_placeholder)))) )
        exact False.elim this)
partial def dFalse (P : Prop) : Decidable P :=
  Decidable.isFalse (fun hp => by
    have e : dTrue P = dFalse P := Subsingleton.elim _ _
    cases hdt : dTrue P with
    | isTrue ht =>
        rw [hdt] at e
        cases hdf : dFalse P with
        | isTrue hf => exact False.elim (by exact False.elim (False.elim (by contradiction)) )
        | isFalse hn =>
            rw [hdf] at e
            cases e
    | isFalse hn => exact hn hp)
end
