import FormalConjectures.Util.ProblemImports

partial def decFalse (P : Prop) : Decidable P :=
  Decidable.isFalse (fun hp => by
    -- try recursive contradiction
    exact match decFalse P with
    | Decidable.isFalse hn => hn hp
    | Decidable.isTrue hp2 => False.elim (by exact decFalse P |>.rec (fun h => ?_) (fun h => ?_)))

#print decFalse
#check decFalse.eq_def

-- Try simple theorem by matching.
theorem notAny (P : Prop) : ¬ P := by
  intro hp
  change False
  -- can we unfold decFalse?
  have d := decFalse P
  cases d with
  | isFalse hn => exact hn hp
  | isTrue hp2 => ?_
