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

def ω : sb := fun (p : Prop) => ∀ (x : U), f x p → p

def δ (S : sb) : Prop := ∀ (p : Prop), S p → p

theorem h_delta : δ ω := by
  intro p H
  apply H (g ω)
  rw [f_g_spec]
  exact H

def S (p : Prop) : Prop := ¬ δ (f (inj p))

noncomputable def A : Prop := δ (f (g S))

-- We want to prove A and ¬ A!
-- First, prove A:
theorem h_A : A := by
  intro p hp
  -- hp has type: f (g S) p, which is equivalent to S p!
  rw [f_g_spec] at hp
  -- hp has type: S p, which is ¬ δ (f (inj p))
  -- We want to prove p!
  -- Let's see: S p is ¬ (∀ q, f (inj p) q → q)
  -- But f (inj p) q is equivalent to p!
  -- So f (inj p) q → q is equivalent to p → q.
  -- So δ (f (inj p)) is ∀ q, p → q, which is ¬ p (if we set q = False).
  -- So S p is ¬ ¬ p!
  -- Thus, from ¬ ¬ p, we can prove p!
  have h_not_not_p : ¬ ¬ p := by
    intro h_not_p
    apply hp
    intro q hq
    rw [f_inj_spec] at hq
    exact False.elim (h_not_p hq)
  exact not_not.mp h_not_not_p

-- Now, prove ¬ A:
theorem h_not_A : ¬ A := by
  intro h_A
  -- h_A is A, which is δ (f (g S))
  -- We want to show False!
  -- Let's apply h_A to some predicate.
  -- Wait, δ (f (g S)) is ∀ p, f (g S) p → p, which is ∀ p, S p → p.
  -- Since S p ↔ ¬ ¬ p, this is ∀ p, ¬ ¬ p → p, which is true!
  -- But wait, we can also prove S (g S) or similar? No, S is a sb, so we can apply S to A!
  -- S A is ¬ δ (f (inj A))
  -- Can we prove S A?
  have h_S_A : S A := by
    rw [S]
    intro h_delta_f_inj_A
    -- h_delta_f_inj_A : ∀ q, f (inj A) q → q
    -- We want to show False!
    -- Since f (inj A) q ↔ A, this is ∀ q, A → q.
    -- So we get A → False (if q = False).
    -- Since we have h_A, we get False!
    apply h_delta_f_inj_A False
    rw [f_inj_spec]
    exact h_A
  -- Now we have h_S_A : S A.
  -- But wait, A is δ (f (g S)), which is ∀ p, S p → p.
  -- So h_A A : S A → A.
  -- Since we have h_S_A, we get A!
  have h_A_val : A := h_A A (by rw [f_g_spec]; exact h_S_A)
  -- But we also have:
  -- S A is ¬ δ (f (inj A))
  -- Wait, if we have h_A_val, can we prove δ (f (inj A))?
  have h_delta_f_inj_A : δ (f (inj A)) := by
    intro q hq
    rw [f_inj_spec] at hq
    exact h_A_val q (by rw [f_g_spec, S]; sorry) -- wait, how to prove f (g S) q?
  sorry
