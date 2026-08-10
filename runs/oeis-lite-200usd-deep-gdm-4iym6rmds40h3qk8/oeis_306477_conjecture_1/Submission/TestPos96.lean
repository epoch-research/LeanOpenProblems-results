open Classical

inductive T : Type 1 where
  | base : T
  | mk : (Type → T) → T

def proj : T → (Type → T)
  | T.base => fun _ => T.base
  | T.mk f => f

-- Ah! `p` is a `Prop` (element of `Type`).
-- So `p` is of type `Type`.
-- But `proj` takes `Type → T`, where the argument is of type `Type` (which is `Type 0` or `Type`).
-- Wait, the argument of `proj` is of type `Type` (which is `Type 0`).
-- Let's check the type of `Type` inside `Type 1`:
-- `Type : Type 1`.
-- So the argument of `T.mk` is `Type → T`, which is `Type 0 → T`.
-- And `p : Prop` has type `Type` (i.e. `Type 0`).
-- So why did Lean say "p has type Prop but is expected to have type Type"?
-- Ah! In `∃ (p : Prop), X = p`, `p` has type `Prop`.
-- But `X` has type `Type`.
-- So `X = p` is a type mismatch because `X` has type `Type` and `p` has type `Prop`!
-- Wait, `Prop` is of type `Type`.
-- But `p` has type `Prop`, so `p` is a TERM of type `Prop`.
-- So `p` is a Proposition (like `True` or `False`).
-- So `p` itself is a Type (specifically a Prop, which is in Type 0).
-- In Lean, is `p` of type `Type`?
-- Yes, `Prop` is a subtype of `Type`, so any term of type `Prop` can be coerced to `Type`.
-- But we can write it explicitly: `PLift p` or `p : Type`?
-- Let's see: `p : Type` coercing works.
-- Let's define the bijection between `(Type → T) → T` and `T`.
-- Wait! We don't need `Prop`!
-- Since we have `T.mk : (Type → T) → T` and `proj : T → (Type → T)` such that `proj (T.mk f) = f` by rfl.
-- We can just do Hurkens' paradox on `T` using `Type` directly!
-- Yes! Hurkens' paradox on `U` with `inj : ((U → Prop) → Prop) → U` can be adapted to `T` with `T.mk : (Type → T) → T`!
-- Let's see how!
-- The type `Type` contains `T → Prop` (since `T : Type 1`, `T → Prop : Type 1`, which is `Type 1`).
-- But wait! `Type` is `Type 0`, so `Type` only contains elements of `Type 0`.
-- `T` is in `Type 1`, so `T → Prop` is in `Type 1`.
-- So `T → Prop` is NOT in `Type 0`!
-- So we cannot pass `T → Prop` as the `Type` argument!
-- Ah! This is why we need `T` to be in `Type 1`, and the constructor to be `(Type 1 → T) → T`!
-- Yes! Let's define `T : Type 2` where `T.mk : (Type 1 → T) → T`!
-- Then `Type 1` contains `T → Prop` (since `T : Type 2`, `T → Prop : Type 2`, which is `Type 2`? No, `Prop` is in `Type 0`, so `T → Prop` is in `Type 2`.
-- Actually, the universe of `T → Prop` is `max 2 0 = 2`. So `T → Prop` is in `Type 1`? No, it is in `Type 2`.
-- Wait, let's keep the universes aligned!
-- Let's define:
--   `T : Type 2`
--   `T.mk : (Type 1 → T) → T`
-- Since `Type 1 : Type 2`, this is perfectly universe-consistent!
-- And `Type 1` contains `Type 0` (which is `Type`).
-- Let's write a file to test this!
