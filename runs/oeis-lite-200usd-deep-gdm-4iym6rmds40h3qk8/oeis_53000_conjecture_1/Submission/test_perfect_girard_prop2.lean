def Set (X : Prop) : Type 0 := X → Prop

def Set_Prop (X : Prop) : Prop := Set X → False

def F (X : Prop) : Prop := (Set_Prop X → X) → Set_Prop X

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
