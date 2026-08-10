import FormalConjectures.Util.ProblemImports

partial def emInl (P : Prop) (_ : Unit) : P ∨ ¬ P :=
  Or.inl (by
    have e := emInl P ()
    cases e with
    | inl p => exact p
    | inr np => exact False.elim (np (by
        have e2 := emInl P ()
        cases e2 with
        | inl p2 => exact p2
        | inr np2 => exact False.elim (np2 (by
            have e3 := emInl P ()
            cases e3 with
            | inl p3 => exact p3
            | inr np3 => exact False.elim (np3 (by
                have e4 := emInl P ()
                cases e4 with
                | inl p4 => exact p4
                | inr np4 => exact False.elim (np4 (by exact False.elim (np4 (by exact False.elim (np4 (by exact False.elim (np4 (by exact False.elim (np4 (by exact False.elim (np4 (by exact False.elim (np4 (by exact False.elim (np4 (by exact False.elim (np4 (by exact False.elim (np4 (by exact p4))))))))))))))))))))))))))))

#print emInl
#print axioms emInl
#check emInl.eq_def
#print emInl.eq_def

theorem proveP (P : Prop) : P := by
  have h := emInl.eq_def P ()
  cases emInl P () with
  | inl p => exact p
  | inr np =>
    rw [h] at np
    contradiction
#print axioms proveP

theorem bad : False := proveP False
#print axioms bad
