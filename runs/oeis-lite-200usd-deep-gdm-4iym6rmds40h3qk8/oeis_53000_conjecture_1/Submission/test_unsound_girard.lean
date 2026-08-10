def Set (X : Type 0) : Prop := X → Prop

def F (X : Type 0) : Prop := (Set (Set X) → X) → Set (Set X)

inductive Unsound : Prop
| mk : (∀ X : Type 0, F X) → Unsound
| base : Unsound
