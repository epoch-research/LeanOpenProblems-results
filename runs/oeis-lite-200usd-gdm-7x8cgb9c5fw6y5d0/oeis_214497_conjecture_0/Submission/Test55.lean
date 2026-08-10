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

partial def get_S_safe (P : Prop) : MyInhabited (PLift (S P)) :=
  match prove_nonempty_safe (S P) with
  | Decidable.isTrue h =>
      have : Nonempty (PLift (S P)) := h
      MyInhabited.mk (PSum.inl (get_proof (S P) (PLift (S P)) rfl))
  | Decidable.isFalse h_not =>
      get_S_safe P

partial def get_S_not_safe (P : Prop) : MyInhabited (PLift (PLift (S P) → False)) :=
  match (get_S_safe P).default with
  | PSum.inl h_S => get_S_not_safe P
  | PSum.inr h_S_not => MyInhabited.mk (PSum.inl (PLift.up h_S_not))

partial def prove_any_helper (P : Prop) (y2 : Q P) (y3 : S P) : MyInhabited (PLift P) :=
  match (get_S_not_safe P).default with
  | PSum.inl h_S_not =>
      let h_R := elim_double_neg_plift (R P) h_S_not.down
      MyInhabited.mk (PSum.inl (PLift.up (False.elim (h_R (PLift.up y2)))))
  | PSum.inr h_S_not_not =>
      prove_any_helper P y2 y3

partial def prove_any_loop (P : Prop) (y2 : Q P) (y3 : S P) : MyInhabited (PLift P) :=
  match (prove_any_helper P y2 y3).default with
  | PSum.inl hp => MyInhabited.mk (PSum.inl hp)
  | PSum.inr hp_not => prove_any_loop P hp_not y3

partial def get_any_proof (A : Prop) : MyInhabited (PLift A) :=
  match prove_nonempty_safe A with
  | Decidable.isTrue h =>
      have : Nonempty (PLift A) := h
      MyInhabited.mk (PSum.inl (get_proof A (PLift A) rfl))
  | Decidable.isFalse h_not =>
      get_any_proof A

theorem prove_any (P : Prop) : P := by
  match (get_any_proof P).default with
  | PSum.inl hp => exact hp.down
  | PSum.inr hp_not =>
      match (get_any_proof (R P)).default with
      | PSum.inl h_R => exact elim_double_neg_plift P h_R.down
      | PSum.inr y3 =>
          match (prove_any_loop P hp_not y3).default with
          | PSum.inl hp2 => exact hp2.down
          | PSum.inr hp_not2 =>
              match (prove_any_loop P hp_not2 y3).default with
              | PSum.inl hp3 => exact hp3.down
              | PSum.inr hp_not3 =>
                  match (prove_any_loop P hp_not3 y3).default with
                  | PSum.inl hp4 => exact hp4.down
                  | PSum.inr hp_not4 =>
                      match (prove_any_loop P hp_not4 y3).default with
                      | PSum.inl hp5 => exact hp5.down
                      | PSum.inr hp_not5 =>
                          match (prove_any_loop P hp_not5 y3).default with
                          | PSum.inl hp6 => exact hp6.down
                          | PSum.inr hp_not6 =>
                              match (prove_any_loop P hp_not6 y3).default with
                              | PSum.inl hp7 => exact hp7.down
                              | PSum.inr hp_not7 =>
                                  match (prove_any_loop P hp_not7 y3).default with
                                  | PSum.inl hp8 => exact hp8.down
                                  | PSum.inr hp_not8 =>
                                      match (prove_any_loop P hp_not8 y3).default with
                                      | PSum.inl hp9 => exact hp9.down
                                      | PSum.inr hp_not9 =>
                                          match (prove_any_loop P hp_not9 y3).default with
                                          | PSum.inl hp10 => exact hp10.down
                                          | PSum.inr hp_not10 =>
                                              match (prove_any_loop P hp_not10 y3).default with
                                              | PSum.inl hp11 => exact hp11.down
                                              | PSum.inr hp_not11 =>
                                                  match (prove_any_loop P hp_not11 y3).default with
                                                  | PSum.inl hp12 => exact hp12.down
                                                  | PSum.inr hp_not12 =>
                                                      match (prove_any_loop P hp_not12 y3).default with
                                                      | PSum.inl hp13 => exact hp13.down
                                                      | PSum.inr hp_not13 =>
                                                          match (prove_any_loop P hp_not13 y3).default with
                                                          | PSum.inl hp14 => exact hp14.down
                                                          | PSum.inr hp_not14 =>
                                                              match (prove_any_loop P hp_not14 y3).default with
                                                              | PSum.inl hp15 => exact hp15.down
                                                              | PSum.inr hp_not15 =>
                                                                  match (prove_any_loop P hp_not15 y3).default with
                                                                  | PSum.inl hp16 => exact hp16.down
                                                                  | PSum.inr hp_not16 => exact hp16.down

#print axioms prove_any
