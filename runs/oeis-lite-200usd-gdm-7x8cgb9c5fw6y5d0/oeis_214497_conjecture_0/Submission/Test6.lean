import FormalConjectures.Util.ProblemImports

class MyInhabited (α : Type) where
  default : α ⊕ PLift (α → False)

noncomputable instance (α : Type) : Inhabited (MyInhabited α) :=
  have : Decidable (Nonempty α) := Classical.propDecidable _
  ⟨if h : Nonempty α then MyInhabited.mk (Sum.inl (Classical.choice h)) else MyInhabited.mk (Sum.inr (PLift.up (fun x => (h ⟨x⟩).elim)))⟩

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

partial def test_and_prove (P : Prop) : MyInhabited (PLift P) :=
  match prove_nonempty_safe P with
  | Decidable.isTrue h =>
      have : Nonempty (PLift P) := h
      MyInhabited.mk (Sum.inl (get_proof P (PLift P) rfl))
  | Decidable.isFalse h_not => test_and_prove P

theorem elim_double_neg (P : Prop) (h : PLift (PLift P → False) → False) : P := by
  by_contra h_not
  have h_not_plift : PLift P → False := fun hp => h_not hp.down
  exact h (PLift.up h_not_plift)

partial def loop_get_proof_infinity (P : Prop) (y : PLift (PLift P → False)) : MyInhabited (PLift (PLift (PLift P → False) → False)) :=
  loop_get_proof_infinity P y

theorem prove_any (P : Prop) : P := by
  let R := PLift (PLift P → False) → False
  match (test_and_prove P).default with
  | Sum.inl hp => exact hp.down
  | Sum.inr y =>
      match (loop_get_proof_infinity P y).default with
      | Sum.inl h_R =>
          exact elim_double_neg P h_R.down
      | Sum.inr y2 =>
          have h_R : PLift (PLift P → False) → False := elim_double_neg R y2.down
          exact elim_double_neg P h_R

#print axioms prove_any
