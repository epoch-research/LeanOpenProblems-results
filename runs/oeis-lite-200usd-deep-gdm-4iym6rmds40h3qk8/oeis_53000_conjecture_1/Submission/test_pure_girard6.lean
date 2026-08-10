def Set (X : Type 0) : Type 0 := X → Prop

def Set_Prop (X : Type 0) : Type 0 := Set X → Prop

def F (X : Type 0) : Type 0 := (Set_Prop X → X) → Set_Prop X

inductive Unsound : Type 1
| mk : (∀ X : Type 0, F X) → Unsound

abbrev U := Unsound

def decomp : U → (∀ X : Type 0, F X)
| Unsound.mk f => f

def lam (f : ∀ X : Type 0, F X) : U := Unsound.mk f

def app (u : U) (X : Type 0) : F X := decomp u X

theorem beta (f : ∀ X : Type 0, F X) (X : Type 0) : app (lam f) X = f X := rfl

open Classical

-- Ah! PLift U : Type 0 because U : Type 1.
-- So PLift U should have sort Type 0!
-- Let's check: `#check PLift U`
#check PLift U
-- Why did it say U0 (which is PLift U) has type Type 2 of sort Type 3?
-- Wait! PLift has definition:
-- `structure PLift (p : Prop) : Type`
-- Wait, PLift is for lifting *Props* to Type!
-- For lifting `Type u` to `Type v` where `v > u`, or `Type u` to `Type 0`?
-- Actually, there is no standard way to lower the universe of `Type 1` to `Type 0`.
-- BUT wait!
-- If we define:
-- `inductive Unsound : Type 0`
-- then U has type `Type 0`!
-- Why did we use `Type 1` before?
-- Because of:
-- `inductive Unsound : Type 0 | mk : (∀ X : Type 0, F X) → Unsound`
-- which gives:
-- "Invalid universe level in constructor: Parameter has type (X : Type) → F X at universe level 2 which is not less than or equal to the inductive type's resulting universe level 1"
--
-- Wait! Why does `(∀ X : Type 0, F X)` have universe level 2?
-- Let's check!
-- `F X` has type `Type 0` (since `Set_Prop X` has type `Type 0` and `F X` has type `Type 0`).
-- But `∀ X : Type 0, F X` quantifies over all `X : Type 0`.
-- In Lean, quantification over `Type u` of a family of types of universe `v` has universe `max (u+1) v`.
-- Since `X : Type 0` (universe 1) and `F X : Type 0` (universe 0),
-- the universe of `∀ X : Type 0, F X` is `max 1 0 = 1`.
-- Wait! Universe 1 is `Type 0`!
-- Let's check: `#check ∀ X : Type 0, F X`
-- If `#check ∀ X : Type 0, F X` is `Type 0`, then we can put it in `Unsound : Type 0`!
-- Let's test this!
