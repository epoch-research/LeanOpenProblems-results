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

-- Let's define inj and proj:
-- We want a retraction between Prop and Unsound:
-- inj : Prop → Unsound
-- proj : Unsound → Prop
-- s.t. proj (inj p) ↔ p.
-- Since Unsound is in Prop, and Prop is in Type 0, inj and proj are both functions in Type 0.
-- Wait, can we define:
-- inj (p : Prop) : Unsound := f_down (fun (q : Prop) => inj (p ∧ q))
-- This is a recursive definition! Will Lean accept it?
-- Since Unsound is a Prop, let's see if we can use `partial def` or just define it?
-- Actually, since Unsound is a Prop, `p ∧ q` is a Prop.
-- Let's see if we can define inj and proj using partial def, or if there is a non-recursive way!
-- Wait, can we define:
-- proj (u : Unsound) : Prop := ∀ (p : Prop), f_up u p = u  -- wait, u has type Unsound. f_up u p has type Unsound.
-- So f_up u p = u is a Prop!
-- Let's see if we can define:
-- inj (p : Prop) : Unsound := f_down (fun _ => inj p) -- wait, this is infinitely recursive.
-- But wait! Since Unsound is a Prop, is there a simpler retraction?
-- What if inj (p : Prop) : Unsound := f_down (fun q => if p then f_down (fun _ => f_down (fun _ => ...)) else ...)
-- Actually, if we have Classical.choice, we can do anything!
-- Wait, since Unsound is a Prop, we can define:
-- noncomputable def inj (p : Prop) : Unsound :=
--   if h : p then
--     -- we need a term of type Unsound.
--     -- But if we have an axiom or a theorem or anything, or we can just use Classical.choice!
--     -- Wait! Classical.choice can give us a term of type Unsound if Nonempty Unsound!
--     -- But is Nonempty Unsound true?
--     -- Yes, because Unsound ↔ (Prop → Unsound).
--     -- Since we have propext and choice, can we prove Nonempty Unsound?
--     -- Let's check!
