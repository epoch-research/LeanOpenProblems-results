inductive Unsound : Type 0
| mk : (Prop → Unsound) → Unsound
| base : Unsound

def decomp : Unsound → (Prop → Unsound)
| Unsound.base => fun _ => Unsound.base
| Unsound.mk f => f

open Classical

noncomputable def inj (p : Prop) : Unsound :=
  Unsound.mk (fun (q : Prop) => if p then Unsound.mk (fun _ => Unsound.base) else Unsound.base)

def proj : Unsound → Prop
| Unsound.base => False
| Unsound.mk _ => True

theorem proj_decomp_inj (p : Prop) (q : Prop) : proj (decomp (inj p) q) ↔ p := by
  dsimp [inj, decomp]
  by_cases h : p
  · rw [if_pos h]
    dsimp [proj]
    exact ⟨fun _ => h, fun _ => True.intro⟩
  · rw [if_neg h]
    dsimp [proj]
    exact ⟨fun h2 => False.elim h2, fun h2 => h h2⟩

abbrev U := Unsound
abbrev sb := (U → Prop) → Prop

noncomputable def g (T : sb) : U := inj (T proj)

noncomputable def f (u : U) : sb :=
  fun (s : U → Prop) => proj (decomp u (s u))

theorem f_g_spec (T : sb) (s : U → Prop) : f (g T) s ↔ T proj :=
  proj_decomp_inj (T proj) (s (inj (T proj)))

def ω : sb := fun (p : U → Prop) => ∀ (x : U), f x p → p x

theorem omega_proj : ω proj := by
  intro x h
  cases x
  · dsimp [f, decomp, proj] at h
    exact False.elim h
  · dsimp [proj]
    trivial
