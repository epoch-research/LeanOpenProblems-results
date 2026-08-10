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

-- Now let's try to prove False!
-- We have f_up : Unsound → Prop → Unsound
-- and f_down : (Prop → Unsound) → Unsound
-- with f_up (f_down x) = x.

-- Let's define:
-- S (p : Prop) : Prop := ¬ (p ↔ True)  -- or similar?
-- Actually, let's use Cantor's diagonal argument!
-- We want to define a function H : Prop → Unsound.
-- But wait! U is in Prop.
-- Let's define:
-- P (u : Unsound) : Prop := ¬ (f_up u u)
-- Wait! f_up u has type Prop → Unsound.
-- But u has type Unsound.
-- So we cannot apply f_up u to u because u is of type Unsound, but f_up u expects a Prop!
-- Ah! But we can map Unsound to Prop!
-- How?
-- We can map u : Unsound to a Prop, say, (u = f_down (fun _ => u))?
-- Or we can map u : Unsound to Prop by:
-- P (u : Unsound) : Prop := (u ↔ True)  -- wait, Unsound is a Prop, so u is already a Prop!
-- OMG!!!
-- Since `Unsound` has sort `Prop`, any element `u : Unsound` is ALREADY a Proposition!
-- So we can apply `f_up u` to `u` directly!!!
-- Yes!!!
-- `f_up u` has type `Prop → Unsound`.
-- Since `u` has type `Unsound` (which has sort `Prop`), `u` is a `Prop`!
-- So `f_up u u` is completely well-typed and has type `Unsound`!
-- Since `Unsound` is a Prop, `f_up u u` is a Prop!
-- So we can define:
-- `P (u : Unsound) : Prop := ¬ (f_up u u)`!
-- Let's check this!!!
