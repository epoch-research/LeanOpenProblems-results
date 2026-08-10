-- Oh! T in Type 1 with mk : (∀ (α : Type) [C α], T) → T is accepted!
-- And it is in Type 1.
-- Let's see: how can we use this to prove False?
-- We can define an instance of `C` for `T`?
-- But `T` is in `Type 1`, and `C` takes `Type 0`!
-- So we can't make `T` an instance of `C`.
-- But we can use `ULift T`!
-- `ULift T` is in `Type 0` (i.e. `Type`).
-- So we can define an instance of `C (ULift T)`!
-- Let's do this!
open Classical

class C (α : Type) where
  f : α → False

inductive T : Type 1 where
  | mk : (∀ (α : Type) [C α], T) → T

def proj (t : T) : ∀ (α : Type) [C α], T
  | T.mk g => g

-- Let's define an instance of C (ULift T) using a function bad : ULift T → False.
-- Since we are in the middle of defining things, we can use `mutual` or `partial def`?
-- But wait! If we have an instance of `C (ULift T)`, then we can construct a term of `T`!
-- How?
-- `T.mk` takes a function `g : ∀ (α : Type) [C α], T`.
-- If we have an instance of `C (ULift T)`, does that help us construct `g`?
-- `g` must return `T` for any `α` with `C α`.
-- If we have `α` and `[inst : C α]`, then we have `inst.f : α → False`.
-- So if we have any element `x : α`, we can get `False` by `inst.f x`, and then use `False.elim` to get `T`!
-- But what if `α` is empty?
-- If `α` is empty, how can we return `T`?
-- We can't!
-- So this `T` is empty, and we can't construct a term of it.
--
-- But wait!
-- What if we define:
--   `inductive T : Type 1 where`
--     `| mk : (∀ (α : Type), (α → T) → T) → T`
-- Here, the argument is `(α → T) → T`.
-- This is strictly positive!
-- And we don't need `C`!
-- Let's check if this is accepted!
