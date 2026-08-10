open Classical

def U : Prop := ∀ p : Prop, ((((p → Prop) → Prop) → p) → p)

noncomputable def le (x : (U → Prop) → Prop) : U :=
  fun p f => f (fun (y : p → Prop) => x (fun (u : U) => y (u p f)))

-- Let's define ge using U's structure!
-- Since U is: ∀ p : Prop, ((((p → Prop) → Prop) → p) → p)
-- If we instantiate p with (U → Prop) → Prop?
-- No, p must be a Prop. But (U → Prop) → Prop has type Type!
--
-- Wait!
-- What if we instantiate p with some Prop that is equivalent to (U → Prop) → Prop?
-- Since U is a Prop, (U → Prop) → Prop is a Type.
-- But wait!
-- If U is a Prop, then U → Prop is also a Type (from U to Prop).
-- Since U has type Prop, it is classically either True or False.
-- If U is True:
--   U → Prop is isomorphic to Prop (which has 2 elements).
--   So (U → Prop) → Prop is isomorphic to Prop → Prop (which has 4 elements).
--   But we can't map Prop → Prop to Prop injectively because Prop has only 2 elements.
-- If U is False:
--   U → Prop is isomorphic to False → Prop, which is isomorphic to Unit (1 element).
--   So (U → Prop) → Prop is isomorphic to Unit → Prop, which is isomorphic to Prop (2 elements).
--   And U has 1 element (False).
--   So again, we can't inject 2 elements into 1 element!
--
-- So classically, in any model of Lean, there is no injection from (U → Prop) → Prop to U!
-- This is a rigorous mathematical proof that U cannot be isomorphic to (U → Prop) → Prop classically.
--
-- BUT wait!
-- Does this mean U is constructive?
-- Yes! If we don't use Classical.choice, can we prove that there is no injection?
-- In constructive logic, we can still prove False from Hurkens' paradox!
-- How does Hurkens' paradox work constructively?
-- It defines:
--   U : Prop := ∀ p : Prop, ((((p → Prop) → Prop) → p) → p)
-- But wait!
-- In Hurkens' paradox, how is `ge` (or projection) defined?
-- Let's look at Coq's/Hurkens' paper!
-- In Coq's standard library, Hurkens' paradox on Prop is defined as:
-- ```coq
-- Definition U : Prop := ∀ p : Prop, ((p → Prop) → p) → p.
-- Definition SB (p : Prop) (f : (p → Prop) → p) (u : U) : Prop :=
--   u (p → Prop) (fun (g : ((p → Prop) → Prop) → p → Prop) => ...).
-- ```
-- Wait!
-- In Coq, `Prop` is at universe level `Prop`, but `p → Prop` is also at universe level `Prop`!
-- Yes! Because Coq has impredicative `Prop`, and `A → Prop` has type `Prop` for ANY type `A`!
-- Wait!
-- Does Lean have impredicative `Prop`?
-- Yes! Lean's `Prop` is impredicative!
-- So for any type `A`, `A → Prop` has type `Prop`!
-- Let's double check this!
-- If `A : Type`, then `A → Prop` has type `Prop`?
-- Let's run `#check U → Prop` in TestPos232.lean!
-- It said `U → Prop : Type`!
-- Ah!
-- In Lean, if `A : Prop`, then `A → Prop : Type`?
-- Let's check!
-- If `A` is `Prop`, then `Prop → Prop` has type `Type`!
-- Oh!
-- In Lean, `Prop` is impredicative, which means if `A : Type u`, then `∀ x : A, Prop` has type `Prop`?
-- No!
-- In Lean, `A → Prop` always has type `Type u` if `A : Type u`!
-- Wait, let's verify this!
-- Let's run a check on `Prop → Prop` in Lean!
