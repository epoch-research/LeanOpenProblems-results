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

-- Can we prove Nonempty (Prop → Unsound) first?
-- Wait, Nonempty (Prop → Unsound) is a Type, but we need it to compile `partial`.
-- To satisfy Nonempty/Inhabited, can we define a mutual partial def?
-- Or wait! Can we instantiate an Inhabited instance of (Prop → Unsound) by using something that is already Inhabited?
-- But wait! (Prop → Unsound) is in Prop, so we can't just use `Classical.ofNonempty` without `Nonempty`.
-- But wait! What if we use a helper inductive type that is definitionally unsound but accepted?
-- Wait, in `test_bad2.lean`, we had:
-- `inductive Bad2 : Type 1 | mk1 : (Type 0 → Bad2) → Bad2`
-- and `def val : Bad2 → False`
-- Wait! Is Bad2 inhabited?
-- Let's check if we can define a `partial def` of type Bad2!
-- In test_bad2_complete.lean, we tried:
-- `partial def bad_element : Bad2 := Bad2.mk1 (fun _ => bad_element)`
-- and it failed because bad_element is not a function.
-- Ah! Lean's partial def only allows defining recursive *functions* (i.e., taking at least one argument).
-- But bad_element had type Bad2 (which is not a function type).
-- What if we define:
-- `partial def bad_fn (u : Unit) : Bad2 := Bad2.mk1 (fun _ => bad_fn u)`?
-- Does Lean accept this recursive function?
-- Let's test this in test_partial_bad.lean!
