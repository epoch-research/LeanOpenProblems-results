inductive Unsound : Type 0
| mk : (Prop → Unsound) → Unsound
| base : Unsound

def decomp : Unsound → (Prop → Unsound)
| Unsound.base => fun _ => Unsound.base
| Unsound.mk f => f

def lam (f : Prop → Unsound) : Unsound := Unsound.mk f

open Classical

noncomputable def inj (p : Prop) : Unsound :=
  if p then Unsound.mk (fun _ => Unsound.mk (fun _ => Unsound.base)) else Unsound.base

def proj : Unsound → Prop
| Unsound.base => False
| Unsound.mk _ => True

theorem proj_inj (p : Prop) : proj (inj p) ↔ p := by
  by_cases h : p
  · have h_inj : inj p = Unsound.mk (fun _ => Unsound.mk (fun _ => Unsound.base)) := by
      dsimp [inj]
      rw [if_pos h]
    rw [h_inj]
    dsimp [proj]
    exact ⟨fun _ => h, fun _ => True.intro⟩
  · have h_inj : inj p = Unsound.base := by
      dsimp [inj]
      rw [if_neg h]
    rw [h_inj]
    dsimp [proj]
    exact ⟨fun h2 => False.elim h2, fun h2 => h h2⟩

abbrev U := Unsound
abbrev sb := Prop → Prop

def f (u : U) (p : Prop) : Prop := proj (decomp u p)

theorem f_inj_spec (p : Prop) (q : Prop) : f (inj p) q ↔ p := by
  by_cases h : p
  · have h_inj : inj p = Unsound.mk (fun _ => Unsound.mk (fun _ => Unsound.base)) := by
      dsimp [inj]
      rw [if_pos h]
    rw [h_inj]
    dsimp [f, decomp, proj]
    exact ⟨fun _ => h, fun _ => True.intro⟩
  · have h_inj : inj p = Unsound.base := by
      dsimp [inj]
      rw [if_neg h]
    rw [h_inj]
    dsimp [f, decomp, proj]
    exact ⟨fun h2 => False.elim h2, fun h2 => h h2⟩

noncomputable def g (T : sb) : U :=
  lam (fun (p : Prop) => inj (T p))

theorem f_g_spec (T : sb) (p : Prop) : f (g T) p ↔ T p := by
  dsimp [f, g, lam, decomp]
  exact proj_inj (T p)

def ω : sb := fun (p : Prop) => ∀ (x : U), f x p → p

def δ (S : sb) : Prop := ∀ (p : Prop), S p → p

theorem h_delta : δ ω := by
  intro p H
  apply H (g ω)
  rw [f_g_spec]
  exact H

def S (p : Prop) : Prop := ¬ δ (f (inj p))

noncomputable def A : Prop := δ (f (g S))

theorem delta_f_inj_iff (p : Prop) : δ (f (inj p)) ↔ ¬ p := by
  dsimp [δ]
  constructor
  · intro h hp
    have h_p := h False
    rw [f_inj_spec] at h_p
    exact h_p hp
  · intro h_not_p r hr
    rw [f_inj_spec] at hr
    exact False.elim (h_not_p hr)

theorem S_spec (p : Prop) : S p ↔ ¬ ¬ p := by
  dsimp [S]
  rw [delta_f_inj_iff]

theorem S_spec_classical (p : Prop) : S p ↔ p := by
  rw [S_spec]
  exact not_not
