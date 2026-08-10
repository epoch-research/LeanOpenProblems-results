def F (X : Prop) : Prop := (((X → Prop) → Prop) → X) → ((X → Prop) → Prop)

inductive Bad : Prop
| mk : (∀ X : Prop, F X) → Bad

abbrev U := Bad

def decomp : U → (∀ X : Prop, F X)
| Bad.mk f => f

def lam (f : ∀ X : Prop, F X) : U := Bad.mk f

def app (u : U) (X : Prop) : F X := decomp u X

theorem beta (f : ∀ X : Prop, F X) (X : Prop) : app (lam f) X = f X := rfl


