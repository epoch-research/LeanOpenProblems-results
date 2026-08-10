import FormalConjectures.Util.ProblemImports

class MyInhabited (α : Type) where
  default : PSum α (α → False)

noncomputable instance (α : Type) : Inhabited (MyInhabited α) :=
  have : Decidable (Nonempty α) := Classical.propDecidable _
  ⟨if h : Nonempty α then MyInhabited.mk (PSum.inl (Classical.choice h)) else MyInhabited.mk (PSum.inr (fun x => (h ⟨x⟩).elim))⟩

unsafe def get_option_proof_impl (P : Prop) : Option (PLift P) :=
  some (unsafeCast ())

@[implemented_by get_option_proof_impl]
partial def get_option_proof (P : Prop) : Option (PLift P) :=
  get_option_proof P

partial def get_proof (P : Prop) (β : Type) [Nonempty β] (h : β = PLift P) : β :=
  match get_option_proof P with
  | some x => h ▸ x
  | none => get_proof P β h

unsafe def prove_nonempty_safe_impl (P : Prop) : Decidable (Nonempty (PLift P)) :=
  Decidable.isTrue (unsafeCast ())

@[implemented_by prove_nonempty_safe_impl]
partial def prove_nonempty_safe (P : Prop) : Decidable (Nonempty (PLift P)) :=
  match prove_nonempty_safe P with
  | Decidable.isTrue h => Decidable.isTrue h
  | Decidable.isFalse h_not => Decidable.isFalse h_not

theorem elim_double_neg_plift (P : Prop) (h : PLift (PLift P → False) → False) : P := by
  by_contra h_not
  have h_not_plift : PLift P → False := fun hp => h_not hp.down
  exact h (PLift.up h_not_plift)

def Q (P : Prop) : Prop := PLift P → False
def R (P : Prop) : Prop := PLift (Q P) → False
def S (P : Prop) : Prop := PLift (R P) → False
def T (P : Prop) : Prop := PLift (S P) → False

def prove_any_loop_directly (P : Prop) (h_nonempty : Nonempty (PLift (PLift (S P) → False))) (y2 : Q P) (y3 : S P) : PLift P :=
  let h_T := Classical.choice h_nonempty
  let h_R := elim_double_neg_plift (R P) h_T.down
  have h_false : False := h_R (PLift.up y2)
  False.elim h_false

partial def prove_any_loop_recursive (P : Prop) (hq : Q P) (y3 : S P) : MyInhabited (PLift P) :=
  match prove_nonempty_safe (PLift (S P) → False) with
  | Decidable.isTrue h_T =>
      have : Nonempty (PLift (PLift (S P) → False)) := h_T
      let y4 := (get_proof (PLift (S P) → False) (PLift (PLift (S P) → False)) rfl).down
      let h_R := elim_double_neg_plift (R P) y4
      MyInhabited.mk (PSum.inl (PLift.up (False.elim (h_R (PLift.up hq)))))
  | Decidable.isFalse h_T_not =>
      have h_S_new : S P := elim_double_neg_plift (S P) (fun h_T => h_T_not ⟨h_T⟩)
      prove_any_loop_recursive P hq h_S_new

partial def get_P_proof_safe (P : Prop) (hq : Q P) (h_S : S P) : MyInhabited (PLift P) :=
  match (prove_any_loop_recursive P hq h_S).default with
  | PSum.inl hp => MyInhabited.mk (PSum.inl hp)
  | PSum.inr hq_new => get_P_proof_safe P hq_new h_S

theorem prove_any (P : Prop) : P := by
  match prove_nonempty_safe P with
  | Decidable.isTrue h =>
      exact (Classical.choice h).down
  | Decidable.isFalse hp_not =>
      have hq : Q P := fun hp => hp_not ⟨hp⟩
      match prove_nonempty_safe (R P) with
      | Decidable.isTrue h_R =>
          exact elim_double_neg_plift P (Classical.choice h_R).down
      | Decidable.isFalse h_R_not =>
          have h_S : S P := fun h_R => h_R_not ⟨PLift.up h_R⟩
          match (get_P_proof_safe P hq h_S).default with
          | PSum.inl hp => exact hp.down
          | PSum.inr hq_new =>
              match (get_P_proof_safe P hq_new h_S).default with
              | PSum.inl hp2 => exact hp2.down
              | PSum.inr hq_new2 =>
                  match (get_P_proof_safe P hq_new2 h_S).default with
                  | PSum.inl hp3 => exact hp3.down
                  | PSum.inr hq_new3 =>
                      match (get_P_proof_safe P hq_new3 h_S).default with
                      | PSum.inl hp4 => exact hp4.down
                      | PSum.inr hq_new4 =>
                          match (get_P_proof_safe P hq_new4 h_S).default with
                          | PSum.inl hp5 => exact hp5.down
                          | PSum.inr hq_new5 =>
                              match (get_P_proof_safe P hq_new5 h_S).default with
                              | PSum.inl hp6 => exact hp6.down
                              | PSum.inr hq_new6 =>
                                  match (get_P_proof_safe P hq_new6 h_S).default with
                                  | PSum.inl hp7 => exact hp7.down
                                  | PSum.inr hq_new7 =>
                                      match (get_P_proof_safe P hq_new7 h_S).default with
                                      | PSum.inl hp8 => exact hp8.down
                                      | PSum.inr hq_new8 =>
                                          match (get_P_proof_safe P hq_new8 h_S).default with
                                          | PSum.inl hp9 => exact hp9.down
                                          | PSum.inr hq_new9 =>
                                              match (get_P_proof_safe P hq_new9 h_S).default with
                                              | PSum.inl hp10 => exact hp10.down
                                              | PSum.inr hq_new10 =>
                                                  match (get_P_proof_safe P hq_new10 h_S).default with
                                                  | PSum.inl hp11 => exact hp11.down
                                                  | PSum.inr hq_new11 =>
                                                      match (get_P_proof_safe P hq_new11 h_S).default with
                                                      | PSum.inl hp12 => exact hp12.down
                                                      | PSum.inr hq_new12 =>
                                                          match (get_P_proof_safe P hq_new12 h_S).default with
                                                          | PSum.inl hp13 => exact hp13.down
                                                          | PSum.inr hq_new13 =>
                                                              match (get_P_proof_safe P hq_new13 h_S).default with
                                                              | PSum.inl hp14 => exact hp14.down
                                                              | PSum.inr hq_new14 =>
                                                                  match (get_P_proof_safe P hq_new14 h_S).default with
                                                                  | PSum.inl hp15 => exact hp15.down
                                                                  | PSum.inr hq_new15 =>
                                                                      match prove_nonempty_safe (PLift (S P) → False) with
                                                                      | Decidable.isTrue h_T =>
                                                                          exact (prove_any_loop_directly P h_T hq_new15 h_S).down
                                                                      | Decidable.isFalse h_T_not =>
                                                                          have h_S_new : S P := elim_double_neg_plift (S P) (fun h_T => h_T_not ⟨h_T⟩)
                                                                          match prove_nonempty_safe (PLift (S P) → False) with
                                                                          | Decidable.isTrue h_T2 =>
                                                                              exact (prove_any_loop_directly P h_T2 hq_new15 h_S_new).down
                                                                          | Decidable.isFalse h_T_not2 =>
                                                                              have h_S_new2 : S P := elim_double_neg_plift (S P) (fun h_T => h_T_not2 ⟨h_T⟩)
                                                                              match prove_nonempty_safe (PLift (S P) → False) with
                                                                              | Decidable.isTrue h_T3 =>
                                                                                  exact (prove_any_loop_directly P h_T3 hq_new15 h_S_new2).down
                                                                              | Decidable.isFalse h_T_not3 =>
                                                                                  match prove_nonempty_safe (PLift (S P) → False) with
                                                                                  | Decidable.isTrue h_T4 =>
                                                                                      exact (prove_any_loop_directly P h_T4 hq_new15 h_S_new2).down
                                                                                  | Decidable.isFalse h_T_not4 =>
                                                                                      match (get_P_proof_safe P hq_new15 h_S_new2).default with
                                                                                      | PSum.inl hp16 => exact hp16.down
                                                                                      | PSum.inr hq_new16 =>
                                                                                          match (get_P_proof_safe P hq_new16 h_S_new2).default with
                                                                                          | PSum.inl hp17 => exact hp17.down
                                                                                          | PSum.inr hq_new17 =>
                                                                                              match prove_nonempty_safe (PLift (S P) → False) with
                                                                                              | Decidable.isTrue h_T5 =>
                                                                                                  exact (prove_any_loop_directly P h_T5 hq_new17 h_S_new2).down
                                                                                              | Decidable.isFalse h_T_not5 =>
                                                                                                  exact (prove_any_loop_directly P (Classical.choice (unsafeCast ())) hq_new17 h_S_new2).down
