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

theorem f_mono (x : U) (A B : U → Prop) (h : ∀ y, A y → B y) : f x A → f x B := by
  dsimp [f, to_Prop]
  cases x with
  | base =>
    dsimp [proj, decomp]
    exact id
  | mk g_val =>
    dsimp [proj, decomp]
    by_cases hA : A (inj True)
    · have hB : B (inj True) := h (inj True) hA
      have heq : A (inj True) = B (inj True) := propext ⟨fun _ => hB, fun _ => hA⟩
      rw [heq]
      exact id
    · by_cases hB : B (inj True)
      · have heq : A (inj True) = B (inj True) := propext ⟨fun _ => hB, fun _ => hA⟩
        rw [heq]
        exact id
      · have heq : A (inj True) = B (inj True) := propext ⟨fun h2 => False.elim (hA h2), fun h2 => False.elim (hB h2)⟩
        rw [heq]
        exact id

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
  rw [f_g_spec]
  intro x H1
  apply H x
  exact f_mono x _ _ (fun y => H (g (f y))) H1

theorem omega_proj : ω proj := by
  intro x
  rcases x with f_val | _
  · intro _
    trivial
  · dsimp [f, decomp, proj, to_Prop]
    intro h
    exact h

theorem girard : False := by
  have h1 : δ ω := h_delta
  have h2 : ¬ δ (f (g ω)) := by
    intro H
    apply H proj
    rw [f_g_spec]
    intro H1
    apply H1
    exact omega_proj
  have h3 : ω (fun y => ¬ δ (f y)) := by
    intro x H1 H2
    apply H1
    rw [f_g_spec]
    intro H3
    apply H2
    rw [f_g_spec]
    intro H4
    apply H3
    intro y H5
    apply H4
    exact H5
  exact h2 (h1 (fun y => ¬ δ (f y)) h3)
