import FormalConjectures.Util.ProblemImports

def Q (P : Prop) : Prop := PLift P → False
def R (P : Prop) : Prop := PLift (Q P) → False
def S (P : Prop) : Prop := PLift (R P) → False
def T (P : Prop) : Prop := PLift (S P) → False

noncomputable instance (P : Prop) : Nonempty (PLift (Q P → T P → P)) := by
  have : Decidable P := Classical.propDecidable P
  match this with
  | Decidable.isTrue h_P =>
      exact ⟨PLift.up (fun _ _ => h_P)⟩
  | Decidable.isFalse h_not_P =>
      have hq : Q P := fun hp => h_not_P hp.down
      have h_R_not : Nonempty (PLift (R P)) → False := by
        intro h_R
        have h_R_val : R P := (Classical.choice h_R).down
        exact h_R_val (PLift.up hq)
      have h_S : S P := fun h_R => h_R_not ⟨PLift.up h_R⟩
      have h_T_not : Nonempty (PLift (T P)) → False := by
        intro h_T
        have h_T_val : T P := (Classical.choice h_T).down
        exact h_T_val (PLift.up h_S)
      exact ⟨PLift.up (fun _ h_T => False.elim (h_T_not ⟨PLift.up h_T⟩))⟩
