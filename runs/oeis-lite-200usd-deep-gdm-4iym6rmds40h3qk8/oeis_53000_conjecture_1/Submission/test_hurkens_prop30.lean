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

abbrev U := Unsound

def to_Prop (T : U → Prop) : Prop := T (inj True)

def f (u : U) (s : U → Prop) : Prop := proj (decomp u (to_Prop s))

theorem f_mono (x : U) (A B : U → Prop) (h : ∀ y, A y → B y) : f x A → f x B := by
  dsimp [f, decomp, to_Prop]
  cases x
  · dsimp [proj]
    intro h1
    exact h1
  · dsimp [proj]
    intro _
    trivial
