inductive T : Type 1 where
  | base : T
  | mk : (Type → T) → T

def proj : T → (Type → T)
  | T.base => fun _ => T.base
  | T.mk f => f

-- Now we have:
--   T.mk : (Type → T) → T
--   proj : T → (Type → T)
--   proj (T.mk f) = f by rfl.

-- Let's define Hurkens' paradox on T!
-- Let's see: we want to prove False.
-- Hurkens' paradox on T requires an injection from ((T → Prop) → Prop) to T.
-- But wait! We have an injection from (Type → T) to T!
-- Since Type is a universe, can we embed (T → Prop) → Prop in Type → T?
-- Yes!
-- For any F : (T → Prop) → Prop, we want to construct a function of type `Type → T`.
-- Let's define `embed (F : (T → Prop) → Prop) : Type → T` as:
--   `embed F (X : Type) : T := ...`
-- How can we use `X : Type` to get `T`?
-- We can decode `T` from `X`!
-- Wait, can we decode `T` from `X`?
-- Yes, if `X = ULift T`?
-- But we don't even need that!
-- Let's see: how can we define `embed`?
-- What if we define:
--   `embed F (X : Type) : T := if X = T then ... else T.base`
-- But wait, `T` is in `Type 1`, not `Type 0` (`Type`)!
-- So `X` (which is of type `Type 0`) can never be equal to `T` (which is of type `Type 1`)!
-- But `ULift T` is in `Type 0`!
-- So `X` can be equal to `ULift T`!
-- Let's check: can we define:
--   `embed F (X : Type) : T := if h : X = ULift T then ... else T.base`
-- Yes! This is type correct!
-- Inside the `then` branch, we have `h : X = ULift T`.
-- We can cast `X` to `ULift T`!
-- But we want to construct a term of `T`.
-- How can we use `F`?
-- `F` has type `(T → Prop) → Prop`.
-- We can define a term of `T` by using `F`!
-- Let's see:
--   `F (fun (t : T) => ...)`
-- This has type `Prop`.
-- How can we turn a `Prop` into `T`?
-- We can define:
--   `prop_to_T (p : Prop) : T := if p then T.mk (fun _ => T.base) else T.base`
-- This is a function of type `Prop → T`!
-- Let's verify this!
