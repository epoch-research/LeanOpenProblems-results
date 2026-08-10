open Classical

inductive T : Type 1 where
  | base : T
  | mk : (Type → T) → T

def proj : T → (Type → T)
  | T.base => fun _ => T.base
  | T.mk f => f

-- Let's define the injection `inj_prop : (Prop → T) → T`
-- and the projection `proj_prop : T → (Prop → T)`.
noncomputable def inj_prop (f : Prop → T) : T :=
  T.mk (fun X => if h : X = Prop then cast (by rw [h]) f True else T.base)

noncomputable def proj_prop (t : T) : Prop → T :=
  fun p => proj t Prop

-- Let's prove proj_prop (inj_prop f) = f?
-- proj_prop (inj_prop f) p
-- = proj (inj_prop f) Prop
-- = (fun X => if h : X = Prop then cast (by rw [h]) f True else T.base) Prop
-- = if h : Prop = Prop then cast (by rw [h]) f True else T.base
-- = f True
-- But we want f p!
-- Ah! We passed `True` inside the cast, not `p`!
-- We need to pass `p`!
-- But `p` has type `Prop`, and `X` is `Prop`.
-- Wait! Inside `fun X => ...`, we don't have `p`.
-- So how can we pass `p`?
-- Wait! The function we are constructing is `Type → T`.
-- To pass `p`, we can encode `p` as the type!
-- Yes! Instead of `X = Prop`, we can use `X = p`? No, `p` is a Prop (element of Type), so `p` is a Type!
-- Yes! In Lean, any Prop is a Type (Prop is Type 0).
-- So `p` is a `Type`!
-- So we can define `fun X => if h : X = p then ... else T.base`?
-- But `inj_prop` doesn't have `p`.
-- But wait!
-- If we want `proj_prop (inj_prop f) p = f p` for any `p : Prop`.
-- Let's define `inj_prop` as:
--   `inj_prop (f : Prop → T) : T := T.mk (fun X => if h : X ∈ {P : Prop | True} then ... else T.base)`
-- Actually, the argument of `T.mk` is `Type → T`.
-- For any `X : Type`, we can check if `X` is a `Prop`?
-- No, we want to know if `X` is a specific Prop `p`.
-- Wait! For any `p : Prop`, `p` is a `Type`.
-- So we can pass `p` as the type argument to `proj`!
-- Yes! `proj_prop t p` is `proj t p`!
-- This is incredibly elegant!
-- Let's define `inj_prop (f : Prop → T) : T := T.mk (fun X => ...)`
-- Since `X` is a `Type`, is `X` also a `Prop`?
-- In Lean, a `Type` `X` is a `Prop` if and only if `X : Prop`.
-- But `X` is just given as `Type`.
-- Can we cast `X` to `Prop`?
-- Yes, classically, we can check if `Nonempty (X = p)` for some `p : Prop`!
-- Since `Prop` is a subset of `Type`, `X` is a `Prop` if and only if `X` is equal to some `p : Prop`.
-- Let's see: if `X` is a `Prop`, we can cast `X` to `Prop` and apply `f` to it!
-- Let's write:
noncomputable def inj_prop (f : Prop → T) : T :=
  T.mk (fun X =>
    if h : ∃ (p : Prop), PLift (X = p) then
      -- If X is a Prop, let's get the Prop p.
      let p := Classical.choose h
      let h_eq : X = p := (Classical.choose_spec h).down
      -- We want to cast f to X → T.
      -- Since X = p, and f has type p → T, we can cast f to X → T!
      let f_cast : X → T := cast (by rw [h_eq]) f
      -- We need an element x : X to apply f_cast to.
      -- Since p is a Prop, if we assume p is true, we can get an element?
      -- But we don't know if p is true.
      -- But wait! If we have `x : X`, we can just do `f_cast x`!
      -- Where do we get `x : X`?
      -- Since `inj_prop` is called as `proj t p` where `X = p`.
      -- If we have an element of `X`?
      -- No, we want `proj_prop t` to have type `Prop → T`.
      -- But wait, `Prop → T` is the type of functions from `Prop` to `T`.
      -- A term `p : Prop` is a TYPE.
      -- So a function of type `Prop → T` takes a PROPOSITION `p : Prop` as argument!
      -- It does NOT take an element of `p`!
      -- Oh! `f` has type `Prop → T`!
      -- So `f` takes `p : Prop` as argument, and returns `T`!
      -- Yes! `f` takes the Proposition `p` itself!
      -- So `f` does NOT need an element of `p`!
      -- It just takes `p`!
      -- So we can just do `f p`!
      -- This is incredibly simple!
      f p
    else
      T.base
  )
