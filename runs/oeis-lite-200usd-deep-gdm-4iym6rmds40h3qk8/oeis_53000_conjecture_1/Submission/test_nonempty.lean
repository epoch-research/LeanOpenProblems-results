inductive Unsound : Prop
| mk : (Prop → Unsound) → Unsound

def val : Unsound → False
| Unsound.mk f => val (f (val (f True) = val (f True)))

def unsound_inhabited : Nonempty (PLift Unsound) := by
  -- Can we prove this?
  sorry
