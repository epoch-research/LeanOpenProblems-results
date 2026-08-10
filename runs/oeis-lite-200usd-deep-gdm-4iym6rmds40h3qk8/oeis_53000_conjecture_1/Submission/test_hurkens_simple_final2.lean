inductive Unsound : Type 0
| mk : (Prop → Unsound) → Unsound
| base : Unsound

def decomp : Unsound → (Prop → Unsound)
| Unsound.base => fun _ => Unsound.base
| Unsound.mk f => f

def lam (f : Prop → Unsound) : Unsound := Unsound.mk f

open Classical

def proj : Unsound → Prop
| Unsound.base => False
| Unsound.mk _ => True

abbrev U := Unsound
abbrev sb := Prop → Prop

def f (u : U) (p : Prop) : Prop := proj (decomp u p)

noncomputable def inj (p : Prop) : Unsound :=
  lam (fun _ => if p then Unsound.mk (fun _ => Unsound.base) else Unsound.base)

theorem proj_inj (p : Prop) : proj (decomp (inj p) True) ↔ p := by
  dsimp [inj, decomp, proj]
  by_cases h : p
  · rw [if_pos h]
    dsimp [proj]
    exact ⟨fun _ => h, fun _ => True.intro⟩
  · rw [if_neg h]
    dsimp [proj]
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
