inductive Unsound : Prop
| mk : (Prop → Unsound) → Unsound
| base : Unsound

theorem decomp : Unsound → (Prop → Unsound)
| Unsound.base => fun _ => Unsound.base
| Unsound.mk f => f

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
abbrev sb := Prop → Prop

def f (u : U) (p : Prop) : Prop := proj (decomp u p)

noncomputable def g (T : sb) : U :=
  Unsound.mk (fun (p : Prop) => inj (T p))

theorem f_g_spec (T : sb) (p : Prop) : f (g T) p ↔ T p := by
  dsimp [f, g, decomp]
  exact proj_inj (T p)

theorem unsound : False := by
  let D (p : Prop) : Prop := ¬ (f p p)
  let d : Prop := g D
  have h_iff : f d d ↔ D d := f_g_spec D d
  have h_contra : f d d ↔ ¬ (f d d) := by
    exact h_iff
  have h_not : ¬ (f d d) := by
    intro h
    exact (h_contra.mp h) h
  exact h_not (h_contra.mpr h_not)

