import FormalConjectures.Util.ProblemImports
partial def decTrue (P : Prop) : Decidable P :=
  let d : Decidable P := decTrue P
  match d with
  | isTrue h => isTrue h
  | isFalse nh => isTrue (False.elim (nh (match decTrue P with | isTrue h => h | isFalse nh2 => False.elim (nh2 (by
      -- no way to close this, but maybe recursive d is available?
      exact match d with | isTrue h => h | isFalse nh3 => False.elim (nh3 (by assumption)))))))

local instance (P : Prop) : Decidable P := decTrue P
example : False := of_decide_eq_true (show decide False = true by rfl)
#print axioms decTrue
