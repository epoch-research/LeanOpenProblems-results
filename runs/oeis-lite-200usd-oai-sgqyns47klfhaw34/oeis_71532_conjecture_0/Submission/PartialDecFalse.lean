import FormalConjectures.Util.ProblemImports

partial def decFalse (P : Prop) : Decidable P :=
  .isFalse (fun _hp : P =>
    match decFalse False with
    | .isTrue hf => hf
    | .isFalse hnf => hnf (by
        -- stuck? need False
        exact False.elim (hnf (by contradiction))))

#print axioms decFalse
#print decFalse

example (P : Prop) : ¬ P := by
  change P → False
  intro hp
  cases decFalse P with
  | isTrue h => exact False.elim (by
      -- no contradiction from hp/h
      exact (by contradiction))
  | isFalse h => exact h hp
