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
      · have heq : A (inj True) = B (inj True) := propext ⟨fun h2 => False.elim (hA h2), fun h2 => False.elim (hB h2)⟩
        rw [heq]
        exact id
      · have heq : A (inj True) = B (inj True) := propext ⟨fun h2 => False.elim (hA h2), fun h2 => False.elim (hB h2)⟩
        rw [heq]
        exact id

theorem h_delta : δ ω := by
  intro p H
  apply H (g ω)
  rw [f_g_spec]
  intro x H1
  apply f_mono x _ _ _ H1
  intro y H2
  exact H (g (f y)) H2

theorem unsound : False := by
  have h_not_omega : ¬ ω (fun x => ¬ δ (f x)) := by
    intro H_omega
    have h_g_not_delta : f (g (fun p => ¬ δ p)) (fun y => ¬ δ (f (g (f y)))) := by
      rw [f_g_spec]
      intro H_delta
      apply H_omega (g (fun p => ¬ δ p))
      · rw [f_g_spec]
        intro x H1
        apply H_omega (g (f x))
        rw [f_g_spec]
        exact H1
      · exact H_delta
    have h_not_delta_g : ¬ δ (f (g (fun p => ¬ δ p))) := by
      intro H_delta
      apply H_delta (fun y => ¬ δ (f y))
      · rw [f_g_spec]
        intro x H1
        apply H_omega (g (f x))
        rw [f_g_spec]
        exact H1
      · exact H_delta
    exact h_not_delta_g (H_omega (g (fun p => ¬ δ p)) h_g_not_delta)
  -- Now we want to prove ω (fun x => ¬ δ (f x))!
  have h_omega : ω (fun x => ¬ δ (f x)) := by
    intro x H1
    intro H_delta
    apply H_delta (fun y => ¬ δ (f y))
    · rw [f_g_spec] at H1
      exact H1
    · exact H_delta
  exact h_not_omega h_omega
