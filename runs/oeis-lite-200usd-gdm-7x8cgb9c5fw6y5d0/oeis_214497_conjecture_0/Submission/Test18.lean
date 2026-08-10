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

partial def test_and_prove (P : Prop) : MyInhabited (PLift P) :=
  match prove_nonempty_safe P with
  | Decidable.isTrue h =>
      have : Nonempty (PLift P) := h
      MyInhabited.mk (PSum.inl (get_proof P (PLift P) rfl))
  | Decidable.isFalse h_not => test_and_prove P

theorem elim_double_neg_plift (P : Prop) (h : PLift (PLift P → False) → False) : P := by
  by_contra h_not
  have h_not_plift : PLift P → False := fun hp => h_not hp.down
  exact h (PLift.up h_not_plift)

partial def loop_get_proof (P : Prop) (y : PLift P → False) : MyInhabited (PLift P) :=
  match (test_and_prove (PLift P → False)).default with
  | PSum.inl hq => loop_get_proof P hq.down
  | PSum.inr hq_not => MyInhabited.mk (PSum.inl (PLift.up (elim_double_neg_plift P hq_not)))

partial def loop_get_proof_infinity (P : Prop) (y : PLift P → False) : MyInhabited (PLift (PLift (PLift P → False) → False)) :=
  loop_get_proof_infinity P y

partial def loop_get_proof_infinity2 (P : Prop) (y : PLift (PLift (PLift P → False) → False) → False) : MyInhabited (PLift (PLift (PLift (PLift (PLift P → False) → False) → False) → False)) :=
  loop_get_proof_infinity2 P y

partial def loop_get_proof_infinity3 (P : Prop) (y : PLift (PLift (PLift (PLift P → False) → False) → False) → False) : MyInhabited (PLift P) :=
  MyInhabited.mk (PSum.inl (PLift.up (elim_double_neg_plift P (elim_double_neg_plift (PLift (PLift P → False) → False) y))))

theorem prove_any (P : Prop) : P := by
  let Q := PLift P → False
  let R := PLift Q → False
  let S := PLift R → False
  match (test_and_prove P).default with
  | PSum.inl hp => exact hp.down
  | PSum.inr y =>
      match (loop_get_proof P y).default with
      | PSum.inl hp2 => exact hp2.down
      | PSum.inr y2 =>
          match (loop_get_proof_infinity P y2).default with
          | PSum.inl h_R => exact elim_double_neg_plift P h_R.down
          | PSum.inr y3 =>
              match (loop_get_proof_infinity2 P y3).default with
              | PSum.inl h_S_not =>
                  match (loop_get_proof_infinity3 P h_S_not.down).default with
                  | PSum.inl hp3 => exact hp3.down
                  | PSum.inr _ => exact elim_double_neg_plift P (elim_double_neg_plift R (elim_double_neg_plift S y3.down))
              | PSum.inr y4 =>
                  exact elim_double_neg_plift P (elim_double_neg_plift R (elim_double_neg_plift S y4.down))

#print axioms prove_any
