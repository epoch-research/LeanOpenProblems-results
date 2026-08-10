def Set (X : Prop) : Type 0 := X → Prop

def Set_Prop (X : Prop) : Prop := Set X → False

def F (X : Prop) : Prop := (Set_Prop X → X) → Set_Prop X

inductive Unsound : Prop
| mk : (∀ X : Prop, F X) → Unsound

theorem unsound_eq : Unsound ↔ (∀ X : Prop, F X) := by
  constructor
  · intro u
    cases u with
    | mk f => exact f
  · exact Unsound.mk

theorem unsound_eq_prop : Unsound = (∀ X : Prop, F X) :=
  propext unsound_eq

def decomp : Unsound → (∀ X : Prop, F X) := cast unsound_eq_prop

def lam (f : ∀ X : Prop, F X) : Unsound := Unsound.mk f

def app (u : Unsound) (X : Prop) : F X := decomp u X

theorem beta (f : ∀ X : Prop, F X) (X : Prop) : app (lam f) X = f X := rfl
