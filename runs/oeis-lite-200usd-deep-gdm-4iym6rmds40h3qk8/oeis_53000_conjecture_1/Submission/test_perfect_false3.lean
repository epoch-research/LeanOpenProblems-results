inductive Unsound : Prop
| mk : (Type 0 → Unsound) → Unsound

def decomp : Unsound → (Type 0 → Unsound)
| Unsound.mk f => f

abbrev U := Unsound

open Classical

noncomputable def S (x : Type 0) : Prop :=
  if h : x = PLift U then
    ¬ (decomp (PLift.down (cast h.symm x)) x)
  else
    False

noncomputable def u_0 : U := Unsound.mk S

theorem unsound_eq : decomp u_0 = S := rfl

theorem unsound : False := by
  have h_S : S (PLift U) ↔ ¬ (decomp u_0 (PLift U)) := by
    dsimp [S]
    rw [dif_pos rfl]
    have h_eq : PLift.down (cast rfl (PLift U)) = u_0 := rfl
    rw [h_eq]
  have h_eq2 : decomp u_0 (PLift U) ↔ S (PLift U) := by
    rw [unsound_eq]
  have h_contra : decomp u_0 (PLift U) ↔ ¬ (decomp u_0 (PLift U)) := by
    rw [h_eq2, h_S]
  have h_not : ¬ (decomp u_0 (PLift U)) := fun h => (h_contra.mp h) h
  have h_val : decomp u_0 (PLift U) := h_contra.mpr h_not
  exact h_not h_val
