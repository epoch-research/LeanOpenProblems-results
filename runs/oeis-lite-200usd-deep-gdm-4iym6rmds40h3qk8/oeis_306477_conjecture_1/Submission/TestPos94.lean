open Classical

inductive T : Type 1 where
  | base : T
  | mk : (Type → T) → T

def proj : T → (Type → T)
  | T.base => fun _ => T.base
  | T.mk f => f

-- Since we want to define `inj_prop (f : Prop → T) : T`,
-- and `proj_prop (t : T) : Prop → T` such that `proj_prop (inj_prop f) = f`.
-- `Prop` is `Type 0`, which is the set of all Propositions.
-- So `Prop → T` is the type of functions that take a Proposition `p : Prop` and return `T`.
-- Note that in Lean, `Prop` itself is of type `Type`.
-- So `Prop → T` is a function of type `Type 0 → T`!
-- And `Type → T` is a function of type `Type 1 → T`!
-- Since `Type 0` is an element of `Type 1` (Prop : Type),
-- we can easily inject `Type 0 → T` into `Type 1 → T`!
-- Yes! Let's define:
noncomputable def inj_prop (f : Prop → T) : Type → T :=
  fun X => if h : X = Prop then f (cast (by rw [h]) (True : Prop)) else T.base
  -- wait, f takes p : Prop. We want to apply f to a Prop.
  -- Since X = Prop, X is Prop.
  -- But we can just use `if h : ∃ (p : Prop), X = p then f (Classical.choose h) else T.base`!
  -- Yes! Let's check!
