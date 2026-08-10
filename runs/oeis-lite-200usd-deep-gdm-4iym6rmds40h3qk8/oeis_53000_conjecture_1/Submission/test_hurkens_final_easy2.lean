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

def S (p : Prop) : Prop := ¬ (f (inj p) True) -- wait! f (inj p) True is equivalent to p!

noncomputable def A : Prop := ∀ (p : Prop), f (g S) p → p

theorem f_inj_True_iff (p : Prop) : f (inj p) True ↔ p := by
  rw [f_inj_spec]

theorem S_spec_classical (p : Prop) : S p ↔ ¬ p := by
  dsimp [S]
  rw [f_inj_True_iff]

theorem A_iff : A ↔ ∀ (p : Prop), ¬ p → p := by
  dsimp [A]
  have h_eq : ∀ (p : Prop), (f (g S) p → p) ↔ (¬ p → p) := by
    intro p
    rw [f_g_spec, S_spec_classical]
  -- wait, can we rewrite or use congr?
  constructor
  · intro h p hp
    have h1 := h p
    rw [f_g_spec, S_spec_classical] at h1
    exact h1 hp
  · intro h p hp
    rw [f_g_spec, S_spec_classical] at hp
    exact h p hp

theorem not_A_True : ¬ A := by
  rw [A_iff]
  intro h
  have h_False := h False id
  exact h_False

-- wait, can we prove A?
-- If we can prove A, then we get False!
-- But A is ∀ p, f (g S) p → p.
-- If p is False, we need f (g S) False → False.
-- Since f (g S) False ↔ S False ↔ ¬ False ↔ True, we need True → False, which is False.
-- So we cannot prove A!
-- Ah! Of course, we cannot prove A because S p = ¬ p is not self-referential enough.
-- We must use the actual self-referential predicate of Hurkens' paradox!
-- Let's check Hurkens' paradox predicate:
-- ω (p : Prop) : Prop := ∀ (x : U), f x p → p
-- δ (S : sb) : Prop := ∀ (p : Prop), S p → p
-- S (p : Prop) : Prop := ¬ δ (f (inj p))  -- wait! This is S p!
-- Let's implement this!
