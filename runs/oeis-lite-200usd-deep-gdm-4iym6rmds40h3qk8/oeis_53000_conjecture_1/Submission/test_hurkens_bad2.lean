inductive Bad2 : Type 1
| mk1 : (Type 0 → Bad2) → Bad2
| base : Bad2

def decomp : Bad2 → (Type 0 → Bad2)
| Bad2.base => fun _ => Bad2.base
| Bad2.mk1 f => f

open Classical

abbrev B := Bad2
abbrev sb := (B → Prop) → Prop

noncomputable def inj_prop (p : Prop) : B :=
  if p then Bad2.mk1 (fun _ => Bad2.base) else Bad2.base

def proj_prop : B → Prop
| Bad2.base => False
| Bad2.mk1 _ => True

theorem proj_inj_prop (p : Prop) : proj_prop (inj_prop p) ↔ p := by
  by_cases h : p
  · have h_inj : inj_prop p = Bad2.mk1 (fun _ => Bad2.base) := by
      dsimp [inj_prop]
      rw [if_pos h]
    rw [h_inj]
    dsimp [proj_prop]
    exact ⟨fun _ => h, fun _ => True.intro⟩
  · have h_inj : inj_prop p = Bad2.base := by
      dsimp [inj_prop]
      rw [if_neg h]
    rw [h_inj]
    dsimp [proj_prop]
    exact ⟨fun h2 => False.elim h2, fun h2 => h h2⟩

def P_B : Type 0 := B → Prop

def f (b : B) (s : B → Prop) : Prop :=
  proj_prop (decomp b P_B s)

noncomputable def g (T : sb) : B :=
  Bad2.mk1 (fun (X : Type 0) =>
    if h : X = P_B then
      inj_prop (T (fun (x : B) => proj_prop (decomp x X (h ▸ (fun _ => False))))) -- wait, what should the argument of decomp be?
    else
      Bad2.base)
