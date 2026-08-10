inductive Bad : Type 1
| mk : (∀ (X : Type 0), (X → Prop) → Prop) → Bad

def decomp : Bad → (∀ (X : Type 0), (X → Prop) → Prop)
| Bad.mk f => f

def lam (f : ∀ (X : Type 0), (X → Prop) → Prop) : Bad :=
  Bad.mk f

def app (b : Bad) (X : Type 0) : (X → Prop) → Prop :=
  decomp b X

theorem beta (f : ∀ (X : Type 0), (X → Prop) → Prop) (X : Type 0) : app (lam f) X = f X := rfl
