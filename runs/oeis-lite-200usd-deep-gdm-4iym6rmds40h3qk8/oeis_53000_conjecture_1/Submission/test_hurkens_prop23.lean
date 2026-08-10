inductive Unsound : Type 0
| mk : (Prop → Unsound) → Unsound
| base : Unsound

def decomp : Unsound → (Prop → Unsound)
| Unsound.base => fun _ => Unsound.base
| Unsound.mk f => f

def lam (f : Prop → Unsound) : Unsound := Unsound.mk f

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

def f (u : U) (p : Prop) : Prop := proj (decomp (decomp u p) p)

noncomputable def g (T : sb) : U :=
  lam (fun (p : Prop) => inj (T (fun (x : U) => f x p)))

theorem f_g_spec (T : sb) (p : Prop) : f (g T) p ↔ T (fun x => f x p) := by
  dsimp [f, g, lam]
  exact proj_decomp_inj (T (fun x => f x p)) p

def f_x_y (y : U) : sb := fun (s : U → Prop) => f y (s y)

def ω (p : U → Prop) : Prop := ∀ (x : U), f x (p (g (f_x_y x))) → p x

def δ (S : sb) : Prop := ∀ (p : U → Prop), S p → p (g S)

theorem h_delta : δ ω := by
  intro p H
  apply H (g ω)
  rw [f_g_spec]
  intro x H1
  dsimp only at H1
  rw [f_g_spec] at H1
  -- Now let's see the type of H1!
  sorry
