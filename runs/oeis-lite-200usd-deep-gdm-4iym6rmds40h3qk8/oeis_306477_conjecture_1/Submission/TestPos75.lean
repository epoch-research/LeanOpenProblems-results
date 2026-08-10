open Classical

inductive T : Type 1 where
  | base : T
  | mk : ((Type → Prop) → Prop) → T

def decomp : T → (Type → Prop) → Prop
  | T.base => fun _ => False
  | T.mk f => f

-- Let's define an injection inj : ((T → Prop) → Prop) → T
-- and a projection proj : T → ((T → Prop) → Prop)
-- such that proj (inj F) = F.
-- Since T is of type Type 1, and Type is of type Type 1, we can't directly put T into Type.
-- But wait! T is in Type 1. And Type is also in Type 1.
-- So we can't put T into Type.
-- But wait, ULift T is in Type!
-- Let's see: `ULift T` has type `Type`.
-- So we can use `ULift T` as a Type!
-- Let's define:
noncomputable def inj (F : ((T → Prop) → Prop)) : T :=
  -- We want to return a term of T.
  -- F has type ((T → Prop) → Prop).
  -- We can use T.mk : ((Type → Prop) → Prop) → T.
  -- So we need to map ((Type → Prop) → Prop) to T.
  -- Let's define a function G : (Type → Prop) → Prop.
  -- G takes H : Type → Prop, and returns a Prop.
  -- How can we define G using F?
  -- We can define G (H : Type → Prop) : Prop :=
  --   F (fun (t : T) => H (unify t)) -- wait, we want to map T to Type.
  -- We can map t : T to `ULift.up t : ULift T`.
  -- Since `ULift T` is of type `Type`, we can pass it to H!
  -- Yes! `ULift.up t` has type `ULift T`, which is a `Type`!
  -- So `H (ULift T)` has type Prop! But wait, `H` takes a `Type` as argument!
  -- Yes! `ULift T` is a `Type`! So `H (ULift T)` is a Prop!
  -- But we wanted a function of type T → Prop.
  -- If we define: `P_of_H (t : T) : Prop := H (ULift T)`? That is constant in t.
  -- Wait, can we map `t : T` to a Type?
  -- Yes! Is there a Type associated with `t`?
  -- What if we define a Type family or use a structure?
  -- Actually, we can define a Type that represents `t`!
  -- For example, `t` can be mapped to a singleton type or a custom type!
  -- But wait, is there a simple way?
  -- What if we just use `inj` and `proj` on `Type`?
  -- Let's see:
  sorry
