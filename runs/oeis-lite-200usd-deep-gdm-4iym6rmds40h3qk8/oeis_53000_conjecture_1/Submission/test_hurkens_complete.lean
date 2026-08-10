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

theorem S_spec_classical (p : Prop) : S p ↔ p := by
  dsimp [S]
  rw [delta_f_inj_iff]
  exact not_not

theorem not_A : ¬ A := by
  intro h_A
  have h_S_A : S A := by
    rw [S_spec_classical]
    exact h_A
  dsimp [S] at h_S_A
  have h_A_inj : ∀ (q : Prop), f (inj A) q → q := by
    intro q hq
    rw [f_inj_spec] at hq
    have h_false : False := by
      apply hq False
      rw [f_g_spec, S_spec_classical]
      exact id
    exact False.elim h_false
  exact h_S_A h_A_inj

theorem A_proof : A := by
  intro p hp
  rw [f_g_spec, S_spec_classical] at hp
  exact hp

theorem unsound : False :=
  not_A A_proof
