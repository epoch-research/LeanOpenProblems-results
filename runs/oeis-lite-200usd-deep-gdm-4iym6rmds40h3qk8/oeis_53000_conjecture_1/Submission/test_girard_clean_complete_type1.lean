def Set (X : Type 0) : Type 0 := X → Prop

def Set_Prop (X : Type 0) : Type 0 := Set X → Prop

def F (X : Type 0) : Type 0 := (Set_Prop X → X) → Set_Prop X

inductive Bad : Type 1
| mk : (∀ (X : Type 0), F X) → Bad

abbrev U := Bad

def decomp : Bad → (∀ (X : Type 0), F X)
| Bad.mk f => f

def lam (f : ∀ (X : Type 0), F X) : Bad :=
  Bad.mk f

def app (b : Bad) (X : Type 0) : F X :=
  decomp b X

theorem beta (f : ∀ (X : Type 0), F X) (X : Type 0) : app (lam f) X = f X := rfl
