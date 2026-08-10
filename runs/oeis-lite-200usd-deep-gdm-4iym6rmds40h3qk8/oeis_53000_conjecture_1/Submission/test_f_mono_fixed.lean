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
      · have heq : A (inj True) = B (inj True) := propext ⟨fun h2 => hB, fun h2 => False.elim (hA h2)⟩
        rw [heq]
        exact id
      · have heq : A (inj True) = B (inj True) := propext ⟨fun h2 => False.elim (hB h2), fun h2 => False.elim (hA h2)⟩
        rw [heq]
        exact id
