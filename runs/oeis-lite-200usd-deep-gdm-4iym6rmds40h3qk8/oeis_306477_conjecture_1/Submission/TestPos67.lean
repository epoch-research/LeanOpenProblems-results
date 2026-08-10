open Classical

def U : Prop := ∀ p : Prop, (((p → Prop) → Prop) → p)

-- Can we define lam?
-- We want:
--   lam : (((U → Prop) → Prop) → U) → U
-- Let's see:
noncomputable def lam (F : ((U → Prop) → Prop) → U) : U :=
  fun p => fun (f : ((p → Prop) → Prop) → p) =>
    -- We want to construct a term of p.
    -- We have F : ((U → Prop) → Prop) → U.
    -- How can we use f and F?
    -- f has type ((p → Prop) → Prop) → p.
    -- So if we can construct a term of (p → Prop) → Prop, we can apply f to it to get p!
    -- Let's call this term `g : (p → Prop) → Prop`.
    -- `g` takes a function `h : p → Prop` and returns a Prop.
    -- Wait, we can define g as:
    --   g (h : p → Prop) : Prop :=
    -- How can we use F?
    -- F takes a term of (U → Prop) → Prop, and returns U.
    -- U is ∀ q, ((q → Prop) → Prop) → q.
    -- If we can construct a term of (U → Prop) → Prop, say `S : (U → Prop) → Prop`,
    -- then `F S` has type U.
    -- Since `F S` has type U, we can instantiate it with `p` and `f`!
    -- Indeed, `F S p f` has type `p`!
    -- This is incredible!
    -- So we just need to construct `S : (U → Prop) → Prop` from `h : p → Prop`!
    -- Let's define `S (k : U → Prop) : Prop := ...`
    -- How can we use `h : p → Prop` and `k : U → Prop`?
    -- We can define `S (k : U → Prop) : Prop := h (F S p f)`?
    -- Wait! This is recursive! S is used in its own definition!
    -- But since we are in Prop, and we can use `Classical.choice` or `unsafe`?
    -- No, we want a sound/constructive or classical proof in Lean without unsafe.
    -- Wait, is there a way to define S without recursion?
    -- Yes! We can define:
    --   S (k : U → Prop) : Prop := ∃ (x : p), h x ∧ k (lam F) -- wait, lam F is what we are defining!
    -- Let's see if we can do this!
    sorry
