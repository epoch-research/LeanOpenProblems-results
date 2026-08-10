open Classical

inductive T : Type 1 where
  | base : T
  | mk : ((Type → Prop) → Prop) → T

def decomp : T → (Type → Prop) → Prop
  | T.base => fun _ => False
  | T.mk f => f

-- Let's define:
-- inj : ((T → Prop) → Prop) → T
-- proj : T → ((T → Prop) → Prop)
-- such that proj (inj F) = F.

-- Can we map T → Prop to Type → Prop?
-- Given P : T → Prop, we want to construct Q : Type → Prop.
-- What if Q (X : Type) : Prop :=
--   ∃ (t : T), X = ULift (PLift (t = t)) ∧ P t ? -- wait, we can encode t in the Type!
-- Yes! We can encode t in the Type!
-- For any t : T, the type `PLift (t = t)` uniquely encodes `t` up to equality!
-- Wait, `PLift (t = t)` is of type `Type`.
-- So we can define:
--   encode (t : T) : Type := PLift (t = t)
-- Can we decode t from `encode t`?
-- Classically, yes!
-- For any `X : Type`, we can check if there exists `t : T` such that `X = PLift (t = t)`.
-- Since `t = t` is unique, we can uniquely decode `t`!
-- Let's define the decoding function:
noncomputable def decode (X : Type) : T :=
  if h : ∃ (t : T), X = PLift (t = t) then
    Classical.choose h
  else
    T.base

theorem decode_encode (t : T) : decode (PLift (t = t)) = t := by
  dsimp [decode]
  split_ifs with h
  · have h_eq := Classical.choose_spec h
    -- h_eq is: PLift (t = t) = PLift (choose h = choose h)
    -- This implies t = choose h!
    -- Let's prove this!
    sorry
  · sorry
