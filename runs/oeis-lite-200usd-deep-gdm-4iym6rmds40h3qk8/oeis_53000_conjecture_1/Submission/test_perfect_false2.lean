inductive Unsound : Prop
| mk : (Type 0 → Unsound) → Unsound

def decomp : Unsound → (Type 0 → Unsound)
| Unsound.mk f => f

theorem unsound_eq : Unsound = (Type 0 → Unsound) := by
  apply propext
  constructor
  · exact decomp
  · exact Unsound.mk

abbrev U := Unsound

def f_up : U → (Type 0 → U) := cast unsound_eq
def f_down : (Type 0 → U) → U := cast unsound_eq.symm

theorem f_up_down (x : Type 0 → U) : f_up (f_down x) = x := by
  rfl

open Classical

noncomputable def S (x : Type 0) : Prop :=
  if h : x = PLift U then
    ∀ (z : PLift U), ¬ (f_up (PLift.down z) (PLift U))
  else
    False

noncomputable def u_0 : U := f_down S

theorem f_up_u_0_spec : f_up u_0 (PLift U) ↔ S (PLift U) := by
  have h : f_up u_0 = S := by
    dsimp [u_0]
    rw [f_up_down]
  rw [h]

theorem S_PLift_U_eq : S (PLift U) ↔ ∀ (z : PLift U), ¬ (f_up (PLift.down z) (PLift U)) := by
  dsimp [S]
  rw [dif_pos rfl]

theorem unsound : False := by
  have h_not : ¬ (f_up u_0 (PLift U)) := by
    intro h
    rw [f_up_u_0_spec] at h
    rw [S_PLift_U_eq] at h
    have h_z0 : PLift U := PLift.up u_0
    have h_contra := h h_z0
    exact h_contra h
  have h_S : S (PLift U) := by
    rw [S_PLift_U_eq]
    intro z
    have h_eq : PLift.down z = u_0 := proof_irrel (PLift.down z) u_0
    rw [h_eq]
    exact h_not
  have h_f_up : f_up u_0 (PLift U) := by
    rw [f_up_u_0_spec]
    exact h_S
  exact h_not h_f_up
