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
  if h : x ↔ Unsound then
    ¬ (cast (propext h).symm x) -- wait, cast takes Unsound to Prop? No, cast goes between types/props
  else
    False
