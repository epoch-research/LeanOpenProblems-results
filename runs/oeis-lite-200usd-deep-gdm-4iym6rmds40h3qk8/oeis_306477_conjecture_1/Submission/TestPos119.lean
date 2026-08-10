open Classical

def U : Prop := ∀ p : Prop, (((p → Prop) → p) → p)

-- lam : ((U → Prop) → U) → U
-- A term of U is `fun p f => ...` which returns `p` (where `f : ((p → Prop) → p) → p`).
-- We can define `lam F p f : p` as:
--   `f (fun (h : p → Prop) => ...)`
-- Since `f` takes a function of type `(p → Prop) → p`,
-- the argument of `f` must take `h : p → Prop` and return `p`!
-- And `F S p f` has type `p`!
-- So we can just return `F S p f`!
-- This is absolutely stunning!
-- Let's check:
--   `S : U → Prop`
--   `S u := h (u p f)`
-- Let's check the types:
--   `u` has type `U`.
--   `u p` has type `((p → Prop) → p) → p`.
--   `u p f` has type `p`.
--   `h` has type `p → Prop`.
--   So `h (u p f)` has type `Prop`!
--   So `S` has type `U → Prop`!
--   So `F S` has type `U`!
--   So `F S p` has type `((p → Prop) → p) → p`.
--   So `F S p f` has type `p`!
-- This is 100% correct and incredibly beautiful!
-- Let's write this down and verify it compiles!
noncomputable def lam (F : (U → Prop) → U) : U :=
  fun p f =>
    f (fun (h : p → Prop) =>
      let S : U → Prop := fun u => h (u p f)
      F S p f
    )
