inductive Unsound : Type 0
| mk : (Prop → Unsound) → Unsound
| base : Unsound

def decomp : Unsound → (Prop → Unsound)
| Unsound.base => fun _ => Unsound.base
| Unsound.mk f => f

def proj : Unsound → Prop
| Unsound.base => False
| Unsound.mk _ => True

open Classical

theorem f_mono (x : Unsound) (P Q : Prop) (h : P → Q) : proj (decomp x P) → proj (decomp x Q) := by
  sorry
