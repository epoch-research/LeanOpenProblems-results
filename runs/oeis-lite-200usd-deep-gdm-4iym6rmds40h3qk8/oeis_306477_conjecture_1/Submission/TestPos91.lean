open Classical

inductive T : Type 1 where
  | base : T
  | mk : (Type → T) → T

def proj : T → (Type → T)
  | T.base => fun _ => T.base
  | T.mk f => f

-- Why is `if Prop = Prop then f True else T.base` not simplifying to `f True`?
-- Because Lean doesn't know that `Prop = Prop` is true?
-- No, `Prop = Prop` is definitionally `True`!
-- Let's prove it by `simp` or `rfl`!
theorem test_if (f : Prop → T) : (if Prop = Prop then f True else T.base) = f True := by
  rfl
