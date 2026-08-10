inductive Unsound : Prop
| mk : (Prop → Unsound) → Unsound

theorem unsound_eq : Unsound ↔ (Prop → Unsound) := by
  constructor
  · intro u
    cases u with
    | mk f => exact f
  · exact Unsound.mk

open Classical

noncomputable def S (x : Prop) : Prop :=
  if h : x = Unsound then
    ¬ (cast h.symm x)
  else
    False
