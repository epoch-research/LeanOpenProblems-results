inductive Unsound : Type 0
| mk : (Prop → Unsound) → Unsound
| base : Unsound

def decomp : Unsound → (Prop → Unsound)
| Unsound.base => fun _ => Unsound.base
| Unsound.mk f => f

def lam (f : Prop → Unsound) : Unsound := Unsound.mk f

open Classical

noncomputable def inj (p : Prop) : Unsound :=
  if p then Unsound.mk (fun _ => Unsound.base) else Unsound.base

def proj : Unsound → Prop
| Unsound.base => False
| Unsound.mk _ => True

theorem proj_inj (p : Prop) : proj (inj p) ↔ p := by
  by_cases h : p
  · have h_inj : inj p = Unsound.mk (fun _ => Unsound.base) := by
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
abbrev sb := (U → Prop) → Prop

def to_Prop (T : U → Prop) : Prop := T (inj True)

def f (u : U) (s : U → Prop) : Prop := proj (decomp u (to_Prop s))

noncomputable def g (T : sb) : U :=
  lam (fun (p : Prop) => inj (T (fun (x : U) => proj (decomp x p))))

theorem f_g_spec (T : sb) (s : U → Prop) : f (g T) s ↔ T (fun x => f x s) := by
  dsimp [f, g, lam, decomp, to_Prop]
  exact proj_inj (T (fun x => proj (decomp x (s (inj True)))))

def ω (p : U → Prop) : Prop := ∀ (x : U), f x (fun y => p (g (f y))) → p x

def δ (S : sb) : Prop := ∀ (p : U → Prop), S p → p (g S)

theorem h_delta : δ ω := by
  intro p H
  apply H (g ω)
  have h1 := f_g_spec ω (fun y => p (g (f y)))
  rw [h1]
  intro x H1
  apply H x
  have h2 := f_g_spec (f x) (fun y => p (g (f y)))
  rw [h2]
  exact H1
