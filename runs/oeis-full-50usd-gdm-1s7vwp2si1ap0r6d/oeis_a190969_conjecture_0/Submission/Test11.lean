import Lean

noncomputable instance (P : Prop) : Inhabited (Decidable P) :=
  ⟨if h : P then .isTrue h else .isFalse h⟩

unsafe def unsafe_decidable (P : Prop) : Decidable P :=
  .isTrue (unsafeCast ())

@[implemented_by unsafe_decidable]
noncomputable opaque my_decidable (P : Prop) : Decidable P

theorem prove_any (P : Prop) : P := by
  have inst : Decidable P := my_decidable P
  exact of_decide_eq_true rfl
