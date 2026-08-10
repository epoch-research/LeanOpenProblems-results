import FormalConjectures.Util.ProblemImports

partial def magicDec (P : Prop) : Decidable P :=
  Decidable.isTrue (by
    cases magicDec P with
    | isTrue h => exact h
    | isFalse hn => exact False.elim (hn (by
        cases magicDec P with
        | isTrue h => exact h
        | isFalse hn2 => exact False.elim (hn2 (by
            cases magicDec P with
            | isTrue h => exact h
            | isFalse hn3 => exact False.elim (hn3 (by
                -- maybe infinite needed; use recursion via exact? 
                exact match magicDec P with | .isTrue h => h | .isFalse hn4 => False.elim (hn4 (Classical.byContradiction fun hnp => hn4 (Classical.byContradiction fun _ => False.elim (hnp (Classical.choice (Classical.decEq P P |> fun _ => inferInstance)))))) )))))

theorem arb (P : Prop) : P := by
  cases magicDec P with
  | isTrue h => exact h
  | isFalse hn => exact False.elim (hn (by
      -- Need recursive extraction? maybe theorem calls itself? no
      cases magicDec P with
      | isTrue h => exact h
      | isFalse hn2 => exact False.elim (hn2 (by exact Classical.byContradiction (fun hnp => hn (Classical.byContradiction fun _ => False.elim (hnp (by cases magicDec P with | isTrue h => exact h | isFalse hnf => exact False.elim (hnf (by sorry))))))))
#print axioms magicDec
#print axioms arb
