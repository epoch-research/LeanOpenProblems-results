inductive Unsound : Prop
| mk : (Prop → Unsound) → Unsound

theorem unsound_eq : Unsound ↔ (Prop → Unsound) := by
  constructor
  · intro u
    cases u with
    | mk f => exact f
  · exact Unsound.mk

open Classical

theorem unsound_eq_prop : Unsound = (Prop → Unsound) :=
  propext unsound_eq

def f_up : Unsound → (Prop → Unsound) := cast unsound_eq_prop
def f_down : (Prop → Unsound) → Unsound := cast unsound_eq_prop.symm

theorem f_up_down (x : Prop → Unsound) : f_up (f_down x) = x := rfl

def P (u : Unsound) : Prop := ¬ (f_up u u)

def p_0 : Unsound := f_down P

theorem contradiction : f_up p_0 p_0 ↔ ¬ (f_up p_0 p_0) := by
  have h_eq : f_up p_0 = P := by
    dsimp [p_0]
    rw [f_up_down]
  -- wait, can we rewrite or dsimp?
  constructor
  · intro h
    have h2 := h
    rw [h_eq] at h2
    -- h2 : P p_0
    -- which is ¬ (f_up p_0 p_0)
    exact h2 h
  · intro h
    -- h : ¬ (f_up p_0 p_0)
    -- which is P p_0
    have h2 : P p_0 := h
    rw [← h_eq] at h2
    exact h2

theorem unsound : False := by
  have h := contradiction
  by_cases h2 : f_up p_0 p_0
  · exact (h.mp h2) h2
  · exact h2 (h.mpr h2)
