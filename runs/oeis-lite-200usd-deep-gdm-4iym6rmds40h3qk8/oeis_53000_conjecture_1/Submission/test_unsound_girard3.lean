def Set (X : Type 0) : Type 0 := X → Prop

def F (X : Type 0) : Type 0 := (Set (Set X) → X) → Set (Set X)

inductive Unsound : Type 0
| mk : (∀ X : Type 0, F X) → Unsound
| base : Unsound
