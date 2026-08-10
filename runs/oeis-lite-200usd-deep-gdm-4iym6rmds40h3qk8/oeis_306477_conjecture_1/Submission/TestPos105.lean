-- Ah! `(α → T) → T` is rejected because `α → T` is on the left side of the arrow `→` in `(α → T) → T`!
-- Yes! Even though `T` is on the right side of `α → T` and `(α → T) → T`,
-- `α → T` as a whole is on the left side of the second `→`.
-- So `T` occurs in a negative position!
-- Yes, the positivity checker correctly detected this!
--
-- But what about:
--   `inductive T : Type 1 where`
--     `| mk : (Type → T) → T`
-- Here, `T` only occurs once, on the right of `→` in `Type → T`.
-- So this is strictly positive!
-- But as we showed, this is still unsound because `Type` contains `T`.
--
-- Let's see: how did we exploit `T.mk : (Type → T) → T` and `proj : T → (Type → T)`?
-- We wanted to define `inj_prop : (Prop → T) → T`.
-- Let's look at `TestPos95.lean` again.
-- The type mismatch was because `p` has type `Prop`, and `X` has type `Type`.
-- But we can use `PLift` to lift `p` to `Type`!
-- `PLift p` has type `Type`!
-- Let's define:
--   `inj_prop (f : (p : Prop) → T) : T := T.mk (fun X => ...)` -- wait, f is a function that takes a Prop as a TYPE?
-- Yes, `f : Prop → T`.
-- `f` takes `p : Prop` and returns `T`.
-- For any `X : Type`, we can check if `X = PLift p` for some `p : Prop`!
-- Let's write:
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

theorem proj_inj_prop (f : Prop → T) : proj_prop (inj_prop f) = f := by
  ext p
  dsimp [proj_prop, inj_prop, proj]
  have h_ex : ∃ (p' : Prop), PLift p = PLift p' := ⟨p, rfl⟩
  rw [dif_pos h_ex]
  have h_eq : p = Classical.choose h_ex := by
    have h_spec := Classical.choose_spec h_ex
    -- h_spec is: PLift p = PLift (choose h_ex)
    -- This implies p = choose h_ex!
    -- Let's prove this!
    sorry
  rw [h_eq]
