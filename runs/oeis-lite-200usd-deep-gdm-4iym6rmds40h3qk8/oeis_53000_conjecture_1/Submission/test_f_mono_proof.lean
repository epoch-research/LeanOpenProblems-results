inductive Unsound : Type 0
| mk : (Prop → Unsound) → Unsound
| base : Unsound

def decomp : Unsound → (Prop → Unsound)
| Unsound.base => fun _ => Unsound.base
| Unsound.mk f => f

open Classical

theorem f_mono (x : Unsound) (P Q : Prop) (h : P → Q) : proj (decomp x P) → proj (decomp x Q) := by
  by_cases hp : P
  · have hq : Q := h hp
    have heq : P = Q := propext ⟨fun _ => hq, fun _ => hp⟩
    rw [heq]
    exact id
  · by_cases hq : Q
    · have heq : P = Q := propext ⟨fun _ => hq, fun _ => hp⟩
      rw [heq]
      exact id
    · have heq : P = Q := propext ⟨fun h2 => False.elim (hp h2), fun h2 => False.elim (hq h2)⟩
      rw [heq]
      exact id

where proj : Unsound → Prop
| Unsound.base => False
| Unsound.mk _ => True
