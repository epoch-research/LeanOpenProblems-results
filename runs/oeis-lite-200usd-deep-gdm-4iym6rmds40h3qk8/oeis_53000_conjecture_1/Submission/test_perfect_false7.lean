inductive Unsound : Prop
| mk : (Prop → Prop) → Unsound

def decomp : Unsound → (Prop → Prop)
| Unsound.mk f => f

abbrev U := Unsound

open Classical

noncomputable def S (x : Prop) : Prop :=
  if h : x = U then
    ¬ (decomp (cast h.symm x) x)
  else
    False

noncomputable def u_0 : U := Unsound.mk S

theorem unsound_eq : decomp u_0 = S := rfl

theorem unsound : False := by
  have h_S : S U ↔ ¬ (decomp u_0 U) := by
    dsimp [S]
    rw [dif_pos rfl]
    have h_eq : cast rfl U = u_0 := rfl
    rw [h_eq]
  have h_eq2 : decomp u_0 U ↔ S U := by
    rw [unsound_eq]
  have h_contra : decomp u_0 U ↔ ¬ (decomp u_0 U) := by
    rw [h_eq2, h_S]
  have h_not : ¬ (decomp u_0 U) := fun h => (h_contra.mp h) h
  have h_val : decomp u_0 U := h_contra.mpr h_not
  exact h_not h_val
