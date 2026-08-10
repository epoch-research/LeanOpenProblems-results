inductive Unsound : Type 0
| mk : (Prop → Unsound) → Unsound
| base : Unsound

def proj : Unsound → Prop
| Unsound.base => False
| Unsound.mk f => ∀ p, proj (f p)

theorem proj_always_false (x : Unsound) : ¬ (proj x) := by
  induction x with
  | base =>
    dsimp [proj]
    exact id
  | mk f ih =>
    dsimp [proj]
    intro h
    have h_true := h True
    exact ih True h_true
