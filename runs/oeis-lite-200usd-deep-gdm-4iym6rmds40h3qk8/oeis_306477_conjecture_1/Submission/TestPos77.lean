open Classical

inductive T : Type 1 where
  | base : T
  | mk : ((Type → Prop) → Prop) → T

def decomp : T → (Type → Prop) → Prop
  | T.base => fun _ => False
  | T.mk f => f

-- Let's define the decoding function using a simpler encoding.
-- What if we use `PLift (t = t)`?
-- We can just define `decode (X : Type) : T` such that if `X = PLift (t = t)` then it returns `t`.
-- Since `X` is a type, can we check if `X` is equal to `PLift (t = t)`?
-- Yes, we can define:
noncomputable def decode (X : Type) : T :=
  if h : ∃ (t : T), X = PLift (t = t) then
    Classical.choose h
  else
    T.base

-- Wait, is PLift (t = t) injective?
-- If PLift (t1 = t1) = PLift (t2 = t2), does t1 = t2?
-- PLift (t1 = t1) is isomorphic to PLift True, which has size 1.
-- So all PLift (t = t) are definitionally/propositionally equal to PLift True!
-- Oh! PLift (t1 = t1) is just PLift True, because t1 = t1 is True!
-- So PLift (t1 = t1) = PLift (t2 = t2) is always true!
-- So this encoding does not uniquely identify t!
--
-- But wait! How can we encode `t : T` in a Type uniquely?
-- What if we use a type family that depends on `t`?
-- For example, what if we define a type `MyType t`?
-- But `MyType t` must be a `Type`.
-- Can we define:
--   MyType (t : T) : Type := PLift (t = t) -- still has only 1 inhabitant.
-- What about a type with `t` in its definition?
-- What if we define:
--   MyType (t : T) : Type := { x : T // x = t }
-- Ah! `{ x : T // x = t }` is a subtype!
-- It is a `Type`!
-- And for two different `t1` and `t2`, `{ x : T // x = t1 }` and `{ x : T // x = t2 }` are different types!
-- In fact, they are only isomorphic, but not equal!
-- Wait, are they equal? No, they are not equal if t1 ≠ t2!
-- Let's check: if `{ x : T // x = t1 } = { x : T // x = t2 }`, does `t1 = t2`?
-- Yes, because if they are equal as types, their underlying sets are equal, so their elements are equal.
-- But wait, in Lean, can we prove that if `{ x : T // x = t1 } = { x : T // x = t2 }` then `t1 = t2`?
-- Let's test this!
