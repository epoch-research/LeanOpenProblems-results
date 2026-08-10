open Classical

inductive T : Type where
  | base : T
  | mk : ((Prop → Prop) → Prop) → T

def decomp : T → (Prop → Prop) → Prop
  | T.base => fun _ => False
  | T.mk f => f

-- Let's define the encoding of t : T as a Prop.
-- What is the simplest way to uniquely encode t as a Prop?
-- Since T has size 2 + (Prop → Prop) → Prop, T is infinite.
-- But Prop has size 2.
-- So we CANNOT inject T into Prop!
-- Wait! Can we inject T → Prop into Prop? No, because T → Prop is larger than T.
-- So we cannot encode T as a Prop.
--
-- But wait!
-- Do we need to encode T as a Prop?
-- No! We want an injection `inj : ((T → Prop) → Prop) → T`!
-- If we have `inj : ((T → Prop) → Prop) → T` and `proj : T → ((T → Prop) → Prop)`
-- such that `proj ∘ inj = id`, then we get a contradiction!
-- Let's see: `T` has `mk : ((Prop → Prop) → Prop) → T`.
-- Can we define `inj` and `proj`?
-- We want to inject `(T → Prop) → Prop` into `(Prop → Prop) → Prop`.
-- Can we inject `(T → Prop) → Prop` into `(Prop → Prop) → Prop`?
-- Since T is larger than Prop, `T → Prop` is larger than `Prop → Prop`.
-- So `(T → Prop) → Prop` is LARGER than `(Prop → Prop) → Prop`.
-- So we CANNOT inject it!
--
-- Wait!
-- What if we use `Type` instead of `Prop`?
--   inductive T : Type 1 where
--     | base : T
--     | mk : ((Type → Prop) → Prop) → T
-- Here, `Type` is in Type 1. `T` is in Type 1.
-- So we want to inject `(T → Prop) → Prop` into `(Type → Prop) → Prop`.
-- Since `Type` is in Type 1, and `T` is in Type 1.
-- Can we inject `T` into `Type`?
-- Yes! For any `t : T`, we can map `t` to `{ x : T // x = t }`!
-- `{ x : T // x = t }` is of type `Type`!
-- This is a nested type, but since it is a subtype, it is in `Type 0` which is `Type`!
-- So we CAN inject `T` into `Type`!
-- Let's define `encode (t : T) : Type := { x : T // x = t }`.
-- Since `encode` is an injection from `T` to `Type`, we can inject `T → Prop` into `Type → Prop`!
-- Let's see: for any `P : T → Prop`, we can define `Q : Type → Prop` as:
--   `Q (X : Type) : Prop := ∃ (t : T), X = { x : T // x = t } ∧ P t`.
-- Since `encode` is injective, `Q (encode t) ↔ P t`!
-- Let's write this down and verify it compiles!
