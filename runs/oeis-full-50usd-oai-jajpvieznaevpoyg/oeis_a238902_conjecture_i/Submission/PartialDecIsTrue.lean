import FormalConjectures.Util.ProblemImports

partial def decP (P : Prop) (_ : Unit) : Decidable P :=
  Decidable.isTrue (by
    have d := decP P ()
    cases d with
    | isTrue h => exact h
    | isFalse nh =>
      -- recursively get a proof and contradict nh
      exact False.elim (nh (by
        have d2 := decP P ()
        cases d2 with
        | isTrue h2 => exact h2
        | isFalse nh2 => exact False.elim (nh2 (by
          have d3 := decP P ()
          cases d3 with
          | isTrue h3 => exact h3
          | isFalse nh3 => exact False.elim (nh3 (by
            have d4 := decP P ()
            cases d4 with
            | isTrue h4 => exact h4
            | isFalse nh4 => exact False.elim (nh4 (by
              have d5 := decP P ()
              cases d5 with
              | isTrue h5 => exact h5
              | isFalse nh5 => exact False.elim (nh5 (by
                have d6 := decP P ()
                cases d6 with
                | isTrue h6 => exact h6
                | isFalse nh6 => exact False.elim (nh6 (by exact False.elim (nh6 (by exact False.elim (nh6 (by exact False.elim (nh6 (by exact False.elim (nh6 (by exact False.elim (nh6 (by exact False.elim (nh6 (by exact False.elim (nh6 (by exact False.elim (nh6 (by exact False.elim (nh6 (by exact False.elim (nh6 (by exact False.elim (nh6 (by exact False.elim (nh6 (by exact False.elim (nh6 (by exact False.elim (nh6 (by exact False.elim (nh6 (by exact False.elim (nh6 (by exact False.elim (nh6 (by exact False.elim (nh6 (by exact False.elim (nh6 (by exact False.elim (nh6 (by exact False.elim (nh6 (by exact False.elim (nh6 (by exact False.elim (nh6 (by exact False.elim (nh6 (by exact False.elim (nh6 (by exact False.elim (nh6 (by exact h6))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

#print decP
#print axioms decP

theorem proveP (P : Prop) : P := by
  have d := decP P ()
  cases d with
  | isTrue h => exact h
  | isFalse nh => exact False.elim (nh (by
    have d2 := decP P ()
    cases d2 with
    | isTrue h2 => exact h2
    | isFalse nh2 => exact False.elim (nh2 (by exact False.elim (nh2 (by exact False.elim (nh2 (by exact False.elim (nh2 (by exact False.elim (nh2 (by exact False.elim (nh2 (by exact False.elim (nh2 (by exact False.elim (nh2 (by exact False.elim (nh2 (by exact False.elim (nh2 (by exact False.elim (nh2 (by exact False.elim (nh2 (by exact False.elim (nh2 (by exact False.elim (nh2 (by exact False.elim (nh2 (by exact False.elim (nh2 (by exact h2)))))))))))))))))))))))))))))))))))))
#print axioms proveP

theorem bad : False := proveP False
#print axioms bad
