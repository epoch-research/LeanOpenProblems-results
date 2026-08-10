import FormalConjectures.Util.ProblemImports

partial def emInl (P : Prop) (_ : Unit) : P ⊕ ¬ P :=
  Sum.inl (by
    have e := emInl P ()
    cases e with
    | inl p => exact p
    | inr np =>
      exact False.elim (np (by
        have e2 := emInl P ()
        cases e2 with
        | inl p2 => exact p2
        | inr np2 => exact False.elim (np2 (by
            have e3 := emInl P ()
            cases e3 with
            | inl p3 => exact p3
            | inr np3 => exact False.elim (np3 (by exact False.elim (np3 (by exact False.elim (np3 (by exact False.elim (np3 (by exact False.elim (np3 (by exact False.elim (np3 (by exact False.elim (np3 (by exact False.elim (np3 (by exact False.elim (np3 (by exact False.elim (np3 (by exact p3))))))))))))))))))))))))

#print emInl
#print axioms emInl
#check emInl.eq_def
#print emInl.eq_def

theorem proveP (P : Prop) : P := by
  have h := emInl.eq_def P ()
  -- h : emInl P () = Sum.inl ...
  cases emInl P () with
  | inl p => exact p
  | inr np =>
    -- rewrite should make impossible?
    rw [h] at np
    contradiction
#print axioms proveP

theorem bad : False := proveP False
#print axioms bad
