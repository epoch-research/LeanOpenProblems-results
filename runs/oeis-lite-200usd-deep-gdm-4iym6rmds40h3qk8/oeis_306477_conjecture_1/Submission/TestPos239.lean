open Classical

inductive T : Type 1 where
  | base : T
  | mk : (Type → T) → T

def proj : T → (Type → T)
  | T.base => fun _ => T.base
  | T.mk f => f

def encode (F : (T → Prop) → Prop) : Type :=
  { f : (T → Prop) → Prop // f = F }

noncomputable def decode (X : Type) : (T → Prop) → Prop :=
  if h : ∃ (F : (T → Prop) → Prop), X = encode F then
    Classical.choose h
  else
    fun _ => False

theorem decode_encode (F : (T → Prop) → Prop) : decode (encode F) = F := by
  dsimp [decode, encode]
  have h : ∃ F', encode F = encode F' := ⟨F, rfl⟩
  rw [dif_pos h]
  have h_spec := Classical.choose_spec h
  let val1 : encode F := ⟨F, rfl⟩
  let val2 : encode (Classical.choose h) := cast h_spec val1
  have h_eq : val2.val = Classical.choose h := val2.property
  have h_cast : val2.val = F := by
    generalize h_spec = eq_proof
    cases eq_proof
    rfl
  rw [← h_cast]
  exact h_eq
