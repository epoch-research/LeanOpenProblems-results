-- Wait, what if we use the fact that `Prop` is impredicative, and we can define `U : Prop`?
-- In `TestPos65.lean`, we showed that `U : Prop := ∀ p : Prop, (((p → Prop) → Prop) → p)` is accepted!
-- And since `U` is in `Prop`, `U → Prop` is in `Type 0` (i.e. `Type`).
-- So `(U → Prop) → Prop` is in `Type 0`!
-- And `((U → Prop) → Prop) → U` is in `Type 0`!
-- So we can define `lam` and `app` for this `U` in `Prop` without any universe issues!
-- Let's see:
--   `U : Prop := ∀ p : Prop, (((p → Prop) → Prop) → p) → p`? No, the definition in `TestPos65.lean` was:
--   `U : Prop := ∀ p : Prop, (((p → Prop) → Prop) → p)`
-- Wait, let's write `TestPos117.lean` to see if we can define `lam` and `app` for this `U`!
open Classical

def U : Prop := ∀ p : Prop, (((p → Prop) → Prop) → p)

-- lam takes F : ((U → Prop) → Prop) → U, and returns U.
-- A term of U is `fun p f => ...` which returns a term of `p` (where `f : ((p → Prop) → Prop) → p`).
-- We can define `lam F p f : p` as:
--   `f (fun (h : p → Prop) => ...)`
-- Inside `fun (h : p → Prop) => ...`, we want to return a Prop.
-- What Prop?
-- We can apply `F` to a term of `(U → Prop) → Prop`!
-- To do so, we need to construct `S : (U → Prop) → Prop` from `h : p → Prop`.
-- `S` takes `k : U → Prop` and returns `Prop`.
-- We can define `S k` as:
--   `∃ (u : U), k u ∧ h (u p f)`?
-- Let's check the types:
--   `u` has type `U`.
--   `u p` has type `((p → Prop) → Prop) → p`.
--   `u p f` has type `p`!
--   `h` has type `p → Prop`.
--   So `h (u p f)` has type `Prop`!
--   And `k u` has type `Prop`.
--   So `k u ∧ h (u p f)` has type `Prop`!
--   So `S k` is a Prop!
-- This is incredibly perfect and 100% type-correct!
-- Let's write this down and verify it compiles!
noncomputable def lam (F : ((U → Prop) → Prop) → U) : U :=
  fun p f =>
    f (fun (h : p → Prop) =>
      let S : (U → Prop) → Prop := fun k => ∃ (u : U), k u ∧ h (u p f)
      F S p f
    )
