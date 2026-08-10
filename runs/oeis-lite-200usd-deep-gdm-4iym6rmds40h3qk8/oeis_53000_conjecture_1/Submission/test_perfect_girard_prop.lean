def Set (X : Prop) : Prop := X → Prop

def F (X : Prop) : Prop := (Set (Set X) → X) → Set (Set X)

inductive Unsound : Prop
| mk : (∀ X : Prop, F X) → Unsound
| base : Unsound

abbrev U := Unsound

def decomp : U → (∀ X : Prop, F X)
| Unsound.base => fun _ => sorry
| Unsound.mk f => f

def lam (f : ∀ X : Prop, F X) : U := Unsound.mk f

def app (u : U) (X : Prop) : F X := decomp u X

theorem beta (f : ∀ X : Prop, F X) (X : Prop) : app (lam f) X = f X := rfl
