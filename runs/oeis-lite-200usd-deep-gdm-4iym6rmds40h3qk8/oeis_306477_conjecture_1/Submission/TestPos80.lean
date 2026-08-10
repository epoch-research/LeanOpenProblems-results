open Classical

inductive T : Type 1 where
  | base : T

-- ULift ({ x : T // x = t }) is in Type (which is Type 0).
-- The signature of ULift is: ULift.{v, u} (α : Type u) : Type (max u v)
-- We want to map Type 1 to Type 0.
-- So u = 1, and we want max 1 v = 0? That is impossible!
-- Ah! We can never map a Type u to a Type v where v < u!
-- This is the core of the universe hierarchy: we can't map Type 1 to Type 0!
-- But wait!
-- Can we encode `t : T` as a Type 0?
-- Since T is in Type 1, can T be mapped to Type 0?
-- No, because T has cardinality larger than Type 0!
-- But wait!
-- If T is in Type, we can map T to Type!
-- Let's define T in Type 0!
--   inductive T : Type where
--     | base : T
--     | mk : ((Type → Prop) → Prop) → T
-- This is rejected by Lean because `Type → Prop` is in Type 1, which is not <= Type 0!
-- Yes, the constructor parameter of `mk` must have a universe level <= the result level.
-- So we can't define T in Type 0.
--
-- But wait!
-- What if we use `Prop` instead of `Type`?
--   inductive T : Type where
--     | base : T
--     | mk : ((Prop → Prop) → Prop) → T
-- This is accepted! And T is in Type 0!
-- And `Prop` is in Type 0!
-- So we can encode `t : T` as a `Prop`!
-- Wait, can we?
-- Yes! `{ x : T // x = t }` is in Type 0, so it is a `Type`!
-- And `t1 = t2` is in `Prop`!
-- So we can use `t = t` or `{ x : T // x = t }`!
-- Let's see if we can do Hurkens' paradox on `T` using `Prop`!
-- To do so, we need `inj : ((T → Prop) → Prop) → T` and `proj : T → ((T → Prop) → Prop)`.
-- Let's write a file to test this!
