-- Let's define the bijection between (Prop → Prop) and a subset of T.
-- Or better, we can inject ((Prop → Prop) → Prop) into T.
-- Since T has a constructor `mk : (Type → T) → T`.
-- Is there an injection from (Prop → T) into Type → T?
-- Yes! Prop is a Type (Prop : Type 0).
-- So we can inject (Prop → T) into Type → T by:
--   `embed_fn (f : Prop → T) (X : Type) : T := if h : X = Prop then f (cast h ...) else T.base`
-- Let's write this down!
open Classical

inductive T : Type 1 where
  | base : T
  | mk : (Type → T) → T

def proj : T → (Type → T)
  | T.base => fun _ => T.base
  | T.mk f => f

noncomputable def embed_fn (f : Prop → T) (X : Type) : T :=
  if h : X = Prop then
    f (cast (by rw [h]) (True : Prop)) -- wait, cast is not quite right
  else
    T.base
