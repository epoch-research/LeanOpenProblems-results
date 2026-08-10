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

theorem S_spec_classical (p : Prop) : S p ↔ ¬ ¬ p := by
  dsimp [S, δ]
  constructor
  · intro h hp
    apply h
    intro q hq
    rw [f_inj_spec] at hq
    exact False.elim (hp hq)
  · intro h_not_not_p h_delta
    apply h_not_not_p
    intro hp
    apply h_delta False
    rw [f_inj_spec]
    exact hp

theorem S_spec (p : Prop) : S p ↔ p := by
  rw [S_spec_classical]
  exact not_not

-- Now we can easily prove False!
theorem unsound : False := by
  -- We know h_delta : δ ω.
  -- By definition of δ ω, we have: ∀ p, ω p → p.
  -- Let's apply this to the prop `A`!
  -- ω A is `∀ (x : U), f x A → A`.
  -- Let's prove `ω A`!
  have h_omega_A : ω A := by
    intro x h_fx_A
    -- x : U
    -- h_fx_A : f x A
    -- We want to prove A, which is δ (f (g S)) = ∀ p, f (g S) p → p.
    intro p hp
    -- hp : f (g S) p, which is S p, which is p!
    rw [f_g_spec, S_spec] at hp
    -- We want to prove p!
    -- Since we have h_fx_A : f x A, can we prove p?
    -- Wait! This is also why we need to use S!
    -- Let's see: `h_delta A h_omega_A` has type `A`!
    -- Let's call it `h_A : A`.
    sorry
  sorry
