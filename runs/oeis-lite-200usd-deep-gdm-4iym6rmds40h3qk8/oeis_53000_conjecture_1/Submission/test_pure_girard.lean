def Set (X : Type 0) : Prop := X → False

def F (X : Type 0) : Prop := (Set (Set X) → X) → Set (Set X)

inductive Unsound : Prop
| mk : (∀ X : Type 0, F X) → Unsound

abbrev U := Unsound

def decomp : U → (∀ X : Type 0, F X)
| Unsound.mk f => f
