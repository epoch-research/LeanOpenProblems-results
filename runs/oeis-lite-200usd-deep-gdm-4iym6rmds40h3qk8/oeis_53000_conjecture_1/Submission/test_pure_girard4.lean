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

-- Now let's implement Girard's paradox using U : Type 1!
-- Wait, does Girard's paradox require any recursive functions?
-- No! Girard's paradox is a pure non-recursive type theory proof of False!
-- Let's construct it!
-- Let G (T : Set_Prop U) (X : Type 0) : F X
-- But wait! T has type Set_Prop U.
-- But U has type Type 1, and Set_Prop expects a Type 0!
-- Ah! Set_Prop U is invalid because Set_Prop only takes Type 0, and U is Type 1.
-- So we need to lift U to Type 0 or use PLift!
-- Let's see: `PLift U` has type Type 0!
-- So we can use `PLift U` instead of `U`!
-- Let's define:
-- `abbrev U0 := PLift U`
-- Let's try to define the operators using U0:
-- `G (T : Set_Prop U0) (X : Type 0) : F X`
-- `τ (T : Set_Prop U0) : U := lam (G T)`
-- `σ (S : U0) : Set_Prop U0 := app (PLift.down S) U0 (PLift.up (τ S))` -- wait, τ S needs S of type Set_Prop U0?
-- Let's write the definitions and see if they typecheck!
