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

def S (p : Prop) : Prop := ¬ (∀ (q : Prop), f (inj p) q → q)

noncomputable def A : Prop := ∀ (p : Prop), f (g S) p → p

theorem delta_f_inj_iff (p : Prop) : (∀ (q : Prop), f (inj p) q → q) ↔ ¬ p := by
  constructor
  · intro h hp
    have h_p := h False
    rw [f_inj_spec] at h_p
    exact h_p hp
  · intro h_not_p r hr
    rw [f_inj_spec] at hr
    exact False.elim (h_not_p hr)

theorem S_spec_classical (p : Prop) : S p ↔ ¬ ¬ p := by
  dsimp [S]
  rw [delta_f_inj_iff]

theorem S_spec (p : Prop) : S p ↔ p := by
  rw [S_spec_classical]
  exact not_not

theorem not_A : ¬ A := by
  intro h_A
  -- h_A : ∀ (p : Prop), f (g S) p → p.
  -- We want to prove False.
  -- Let's apply h_A to A!
  -- h_A A : f (g S) A → A.
  -- Since f (g S) A ↔ S A ↔ A.
  -- So h_A A : A → A. This is a tautology.
  -- But wait! S A is ¬ (∀ (q : Prop), f (inj A) q → q).
  -- Since we have h_A, we can prove (∀ (q : Prop), f (inj A) q → q)!
  have h_delta_f_inj_A : ∀ (q : Prop), f (inj A) q → q := by
    intro q hq
    rw [f_inj_spec] at hq
    -- hq : A. We want to prove q.
    -- Since we have hq : A, we can apply hq to q!
    -- hq q : f (g S) q → q.
    -- Since f (g S) q ↔ S q ↔ q.
    -- So hq q : q → q. This is also a tautology.
    -- But wait! Can we prove f (g S) q?
    -- No, f (g S) q is S q.
    -- Let's see: how to prove q from hq?
    -- If we have h_A, we can also prove ¬ A!
    -- Yes! We can prove ¬ A by showing S A!
    -- But how do we prove S A?
    -- S A is ¬ (∀ q, f (inj A) q → q).
    -- Suppose h_all : ∀ q, f (inj A) q → q.
    -- Then we can show False!
    -- Since h_all False : f (inj A) False → False.
    -- And f (inj A) False ↔ A.
    -- So we have A → False.
    -- Since we have h_A : A, we get False!
    -- This is incredibly beautiful! Let's write this down!
    sorry
  sorry
