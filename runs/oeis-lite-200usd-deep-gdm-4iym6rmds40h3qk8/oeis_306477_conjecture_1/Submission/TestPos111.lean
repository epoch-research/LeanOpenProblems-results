open Classical

inductive T : Type 1 where
  | base : T
  | mk : (Type → T) → T

def proj : T → (Type → T)
  | T.base => fun _ => T.base
  | T.mk f => f

noncomputable def inj_prop (f : Prop → T) : T :=
  T.mk (fun X =>
    if h : ∃ (p : Prop), X = PLift p then
      f (Classical.choose h)
    else
      T.base
  )

noncomputable def proj_prop (t : T) : Prop → T :=
  fun p => proj t (PLift p)

theorem PLift_inj (p1 p2 : Prop) (h : PLift p1 = PLift p2) : p1 = p2 := by
  have h1 : p1 ↔ p2 := by
    constructor
    · intro hp1
      let val : PLift p2 := cast h (PLift.up hp1)
      exact val.down
    · intro hp2
      let val : PLift p1 := cast h.symm (PLift.up hp2)
      exact val.down
  exact propext h1

theorem proj_inj_prop (f : Prop → T) : proj_prop (inj_prop f) = f := by
  ext p
  dsimp [proj_prop, inj_prop, proj]
  have h_ex : ∃ (p' : Prop), PLift p = PLift p' := ⟨p, rfl⟩
  rw [dif_pos h_ex]
  have h_spec := Classical.choose_spec h_ex
  have h_eq : p = Classical.choose h_ex := PLift_inj p (Classical.choose h_ex) h_spec
  generalize Classical.choose h_ex = q at *
  cases h_eq
  rfl

-- Now we have:
--   inj_prop : (Prop → T) → T
--   proj_prop : T → (Prop → T)
--   proj_inj_prop : ∀ f, proj_prop (inj_prop f) = f

-- Let's define the standard Hurkens' paradox on U = Prop.
-- But here we have T instead of Prop.
-- Wait! Can we map T to Prop?
-- Yes, we showed we can map Prop to T and back!
-- But wait, we can just do Hurkens' paradox on T itself!
-- Wait, Hurkens' paradox on T requires an injection from ((T → Prop) → Prop) to T.
-- Do we have this?
-- We have `inj_prop : (Prop → T) → T` and `proj_prop : T → (Prop → T)`.
-- Let's see: `Prop → T` is of type `Type 1`.
-- And `(T → Prop) → Prop` is of type `Type 1`.
-- Can we map `(T → Prop) → Prop` to `Prop → T`?
-- Let's see: we want `F : ((T → Prop) → Prop) → (Prop → T)`.
-- Let `S : (T → Prop) → Prop`.
-- We want to construct a function of type `Prop → T`.
-- Given `p : Prop`, we want to return `T`.
-- Since `p` is a Prop, if `p` is True, we can use `S` to get a Prop, and map it to `T`?
-- Wait, how can we use `S`?
-- `S` takes `P : T → Prop` and returns `Prop`.
-- If we define:
--   `F (S) (p) := if p is True then T.base else T.base`? That's constant.
-- But wait!
-- Can we just do Cantor's paradox on `Prop → T`?
-- Let's see: we have `inj_prop : (Prop → T) → T` and `proj_prop : T → (Prop → T)`.
-- This means `Prop → T` is injected into `T`!
-- Since `Prop → T` is injected into `T`, we can define a map from `Prop → T` to `Prop → Prop`?
-- Yes, since we can map `T` to `Prop` and back!
-- Let's define `T_to_prop (t : T) : Prop := (t = T.base)`? No, we want a bijection or injection.
-- We can map `T` to `Prop` by `T_to_prop` and `Prop` to `T` by `prop_to_T`!
-- We proved in `TestPos88.lean`:
--   `T_to_prop (prop_to_T p) ↔ p`.
-- So `Prop` is injected into `T`, and `T` is projected to `Prop`!
-- So we can map `Prop → T` to `Prop → Prop` and back!
-- In fact:
--   `inj_prop` gives us a map from `Prop → T` to `T`.
--   `proj_prop` gives us a map from `T` to `Prop → T`.
-- Let's define:
--   `inj_PP (f : Prop → Prop) : Prop := T_to_prop (inj_prop (fun p => prop_to_T (f p)))`
--   `proj_PP (p : Prop) : Prop → Prop := fun q => T_to_prop (proj_prop (prop_to_T p) q)`
-- Let's check if `proj_PP (inj_PP f) = f`!
-- `proj_PP (inj_PP f) q`
-- `= T_to_prop (proj_prop (prop_to_T (inj_PP f)) q)`
-- Wait, `prop_to_T (inj_PP f)` is `prop_to_T (T_to_prop (inj_prop ...))`.
-- Since `prop_to_T (T_to_prop t) ↔ t`?
-- No! `prop_to_T (T_to_prop t) ↔ t` is NOT true in general because `T` is larger than `Prop`.
-- But wait!
-- We only need `T_to_prop (prop_to_T p) ↔ p`!
-- Let's see:
-- `inj_PP (f : Prop → Prop) : Prop` is defined.
-- But wait! `proj_PP` takes `p : Prop`.
-- Can we define `inj_PP : (Prop → Prop) → Prop`?
-- If we can define `inj_PP : (Prop → Prop) → Prop` and `proj_PP : Prop → (Prop → Prop)`
-- such that `proj_PP (inj_PP f) = f`.
-- Then we have injected `Prop → Prop` into `Prop`!
-- This is a DIRECT cardinality contradiction on `Prop`!
-- And it is completely in `Prop`!
-- Let's see if we can do this!
-- Let's define:
--   `inj_P (f : Prop → Prop) : T := inj_prop (fun p => prop_to_T (f p))`
--   `proj_P (t : T) : Prop → Prop := fun p => T_to_prop (proj_prop t p)`
-- Then:
-- `proj_P (inj_P f) p`
-- `= T_to_prop (proj_prop (inj_prop (fun p' => prop_to_T (f p'))) p)`
-- Since `proj_prop (inj_prop g) = g`, this is:
-- `= T_to_prop (prop_to_T (f p))`
-- Since `T_to_prop (prop_to_T x) ↔ x`, this is:
-- `= f p`!
-- Oh my god!
-- This is a complete, perfect, 100% exact projection and injection between `Prop → Prop` and `T`!
--   `inj_P : (Prop → Prop) → T`
--   `proj_P : T → (Prop → Prop)`
--   `proj_inj_P : ∀ f, proj_P (inj_P f) = f`!
--
-- This is incredibly simple and beautiful!
-- Let's write a file to verify this!
