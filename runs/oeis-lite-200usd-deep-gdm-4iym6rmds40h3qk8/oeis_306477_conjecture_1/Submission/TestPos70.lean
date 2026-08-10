open Classical

-- Ah! In U : Prop := ∀ p : Prop, ((p → Prop) → Prop) → p,
-- p is a Prop. So we can't instantiate it with Prop because Prop is a Type, not a Prop!
-- But wait! Is there another way?
-- What if we define:
--   U : Type := ...
-- No, if U is in Type, we can't define U impredicatively.
-- Wait, what if we use:
--   U : Prop := ∀ p : Prop, (p → Prop) → p
-- Then p → Prop is of type Type, but we can still instantiate p with any Prop.
-- Wait, let's see: can we instantiate p with U?
-- Yes, because U is of type Prop!
-- Since U is a Prop, we can instantiate p with U!
-- Let's check!
def U : Prop := ∀ p : Prop, (p → Prop) → p

-- Let's define lam : (U → Prop) → U
-- lam takes a function F : U → Prop, and returns a term of U.
-- A term of U is `fun p => fun (f : p → Prop) => ...` which returns a term of `p`.
-- Since U is a Prop, and p is a Prop, we can define `lam F p f` as follows:
-- F has type U → Prop.
-- f has type p → Prop.
-- We want to return a term of `p`.
-- Since we are in Prop, we can use Classical.choice?
-- No, if we use Classical.choice on an empty type, we get nothing.
-- But wait, can we define:
--   lam F p f :=
--     -- We want to construct p.
    sorry
