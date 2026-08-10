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
| Unsound.mk f => ∀ p, proj (f p)

abbrev U := Unsound
abbrev sb := Prop → Prop

def f (u : U) (p : Prop) : Prop := proj (decomp u p)

theorem f_base (p : Prop) : f Unsound.base p = False := rfl

theorem proj_eq_all_f (x : U) : proj x ↔ ∀ p, f x p := by
  cases x with
  | base =>
    dsimp [proj, f, decomp]
    exact ⟨fun h => False.elim h, fun h => h True⟩
  | mk f_val =>
    dsimp [proj, f, decomp]
    exact ⟨fun h => h, fun h => h⟩

theorem proj_inj_false : proj (inj False) ↔ False := by
  have h_inj : inj False = Unsound.base := by
    dsimp [inj]
    rw [if_neg id]
  rw [h_inj]
  dsimp [proj]
  exact ⟨fun h => h, fun h => False.elim h⟩

noncomputable def g (T : sb) : U :=
  lam (fun (p : Prop) => inj (T p))

theorem f_g_spec (T : sb) (p : Prop) : f (g T) p ↔ proj (inj (T p)) := by
  dsimp [f, g, lam, decomp]
  exact Iff.rfl
