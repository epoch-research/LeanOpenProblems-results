open Classical

inductive T : Type 2 where
  | base : T
  | mk : (Type 1 → T) → T

def proj : T → (Type 1 → T)
  | T.base => fun _ => T.base
  | T.mk f => f

-- Now we have:
--   T.mk : (Type 1 → T) → T
--   proj : T → (Type 1 → T)
--   proj (T.mk f) = f by rfl.

-- Let's define the bijection between Prop → T and Type 1 → T.
-- No, we want a bijection between (T → Prop) and Type 1.
-- Since `T : Type 2`, `T → Prop` is in `Type 2` (its universe is max 2 0 = 2).
-- Wait! `T → Prop` is in `Type 1`? No, because `T` is in `Type 2`, `T → Prop` is in `Type 2`.
-- But `Type 1` is in `Type 2`.
-- Can we inject `T → Prop` into `Type 1`?
-- `T → Prop` has universe level 2, so it cannot be in `Type 1` (which has universe level 2? No, `Type 1 : Type 2`).
-- Let's check the universes:
-- `T : Type 2` (i.e. `T : Sort 3`).
-- `Prop : Type 0` (i.e. `Prop : Sort 1`).
-- `T → Prop` has type `Sort (max 3 1) = Sort 3 = Type 2`.
-- So `T → Prop` is in `Type 2` (it is a term of `Type 2`, i.e., `T → Prop : Type 2`).
-- `Type 1` is `Sort 2`. As a term, `Type 1 : Type 2`.
-- So both `T → Prop` and `Type 1` are terms of `Type 2`.
-- Since they are both types in `Type 2`, can we inject `T → Prop` into `Type 1`?
-- Since `Type 1` is strictly smaller than `Type 2`, can we inject `T → Prop` into `Type 1`?
-- No, because `T → Prop` is in `Type 2`, so it is larger than `Type 1`!
--
-- Ah! But wait!
-- What if we define:
--   `T : Type 1`
--   `T.mk : (Type → T) → T`
-- Here:
-- `T : Type 1` (i.e. `T : Sort 2`).
-- `T → Prop` has type `Sort (max 2 1) = Sort 2 = Type`.
-- So `T → Prop : Type`!
-- And `Type` (which is `Type 0` / `Sort 1`) is also in `Type 1` (i.e., `Type : Type 1`).
-- So both `T → Prop` and `Type` are in `Type 1`!
-- Since `T → Prop` is in `Type` (Type 0), and `Type` is the set of all types in `Type 0`.
-- This means `T → Prop` is an element of `Type`!
-- Yes! `T → Prop : Type`!
-- So `T → Prop` IS a Type!
-- So we can pass `T → Prop` directly as the `Type` argument!
-- Oh my god!
-- This is incredibly beautiful!
-- Since `T → Prop` is in `Type`, we can just pass `T → Prop` as the argument to `proj`!
-- Let's check:
-- `proj t (T → Prop)` is completely type-correct!
-- Let's verify this!
