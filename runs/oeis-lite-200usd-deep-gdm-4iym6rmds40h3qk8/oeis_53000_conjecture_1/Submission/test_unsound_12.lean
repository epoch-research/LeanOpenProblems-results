inductive Bad (F : Type 0 → Type 0) : Type 1
| mk : (∀ X : Type 0, F X → Bad F) → Bad F

def F (X : Type 0) : Type 0 := (((X → Prop) → Prop) → X) → ((X → Prop) → Prop)

abbrev U := Bad F

def decomp : U → (∀ X : Type 0, F X → U)
| Bad.mk f => f

def lam (f : ∀ X : Type 0, F X → U) : U := Bad.mk f

def app (u : U) (X : Type 0) (f : F X) : U := decomp u X f

theorem beta (f : ∀ X : Type 0, F X → U) (X : Type 0) (x : F X) : app (lam f) X x = f X x := rfl

