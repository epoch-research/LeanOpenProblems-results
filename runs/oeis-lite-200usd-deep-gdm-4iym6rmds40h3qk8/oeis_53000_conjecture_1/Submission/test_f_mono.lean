inductive Unsound : Type 0
| mk : (Prop → Unsound) → Unsound
| base : Unsound

def decomp : Unsound → (Prop → Unsound)
| Unsound.base => fun _ => Unsound.base
| Unsound.mk f => f

open Classical

noncomputable def inj (p : Prop) : Unsound :=
  Unsound.mk (fun (q : Prop) => if p then Unsound.mk (fun _ => Unsound.base) else Unsound.base)

def proj : Unsound → Prop
| Unsound.base => False
| Unsound.mk _ => True

abbrev U := Unsound
def f (u : U) (p : Prop) : Prop := proj (decomp (decomp u p) p)

theorem f_mono (x : U) (A : Prop) : f x (f x A) → f x A := by
  dsimp [f, decomp]
  cases x
  · dsimp [proj]
    intro h
    exact h
  · dsimp [proj]
    intro _
    trivial
