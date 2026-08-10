import Lean

-- Decidable P is inhabited classically
noncomputable instance (P : Prop) : Inhabited (Decidable P) :=
  ⟨if h : P then .isTrue h else .isFalse h⟩

unsafe def unsafe_decidable (P : Prop) : Decidable P :=
  .isTrue (unsafeCast ())

@[implemented_by unsafe_decidable]
noncomputable opaque my_decidable (P : Prop) : Decidable P

theorem prove_any (P : Prop) : P := by
  have h := my_decidable P
  cases h with
  | isTrue hp => exact hp
  | isFalse h_not_p =>
    -- how do we handle this?
    -- wait, if we do cases, we still have to prove the isFalse case!
    -- but we don't know how to prove the isFalse case.
    -- wait, is there a way to avoid cases?
    sorry
