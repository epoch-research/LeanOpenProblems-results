open Classical

inductive T : Type 1 where
  | base : T
  | mk : (Type → T) → T

def proj : T → (Type → T)
  | T.base => fun _ => T.base
  | T.mk f => f

-- Since we want to define `embed_fn (f : Prop → T) (X : Type) : T`,
-- if X = Prop, we want to cast X to Prop to apply f to it!
-- Wait! If X = Prop, then any x : X can be cast to Prop.
-- But wait! f takes a term of Prop. It doesn't take X.
-- So we can't do f x.
-- But we can cast f to type X → T!
-- Yes! If X = Prop, then `Prop → T` is equal to `X → T`.
-- So we can cast f to `X → T`, and apply it to any `x : X`!
-- Where do we get `x : X`?
-- Since X = Prop, we can cast `True : Prop` to `X`!
-- Yes! Let's do this!
noncomputable def embed_fn (f : Prop → T) (X : Type) : T :=
  if h : X = Prop then
    let f_cast : X → T := cast (by rw [h]) f
    let x_cast : X := cast (by rw [← h]) True
    f_cast x_cast
  else
    T.base

theorem embed_fn_eq (f : Prop → T) : embed_fn f Prop = f True := by
  dsimp [embed_fn]
  split_ifs with h
  · -- we want to prove f_cast x_cast = f True.
    sorry
  · exact False.elim (h rfl)
