import Mathlib

def C : Prop := 1 + 1 = 3

def r (x y : Prop) : Prop := (x = y) ∨ C

theorem g_respects (x y : Prop) (h : r x y) : (x ∨ C) = (y ∨ C) := by
  cases h with
  | inl h_eq => rw [h_eq]
  | inr h_C =>
    have hx : x ∨ C := Or.inr h_C
    have hy : y ∨ C := Or.inr h_C
    have hx_eq : (x ∨ C) = True := propext ⟨fun _ => trivial, fun _ => hx⟩
    have hy_eq : (y ∨ C) = True := propext ⟨fun _ => trivial, fun _ => hy⟩
    rw [hx_eq, hy_eq]

noncomputable def f : Quot r → Prop := Quot.lift (fun (x : Prop) => x ∨ C) g_respects

theorem f_true : f (Quot.mk r True) = (True ∨ C) := rfl
theorem f_false : f (Quot.mk r False) = (False ∨ C) := rfl

theorem C_of_eq (h_eq : Quot.mk r True = Quot.mk r False) : C := by
  have h_f : (True ∨ C) = (False ∨ C) := congrArg f h_eq
  have h_true_or_C : True ∨ C := Or.inl trivial
  have h_false_or_C : False ∨ C := h_f ▸ h_true_or_C
  cases h_false_or_C with
  | inl h_false => exact False.elim h_false
  | inr h_C => exact h_C


#print axioms C_of_eq


