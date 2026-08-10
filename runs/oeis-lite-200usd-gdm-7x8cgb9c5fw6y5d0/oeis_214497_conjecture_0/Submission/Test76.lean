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

theorem prove_any (P : Prop) : P := by
  match (test_and_prove P).default with
  | PSum.inl hp => exact hp.down
  | PSum.inr hp_not =>
      exact (@Classical.choice (PLift P) (by
        match (test_and_prove P).default with
        | PSum.inl hp2 => exact ⟨hp2⟩
        | PSum.inr _ => exact (@Classical.choice (Nonempty (PLift P)) (unsafeCast ()))
      )).down
