def Set (X : Type 0) : Type 0 := X → Prop

def F (X : Type 0) : Type 0 := (Set (Set X) → X) → Set (Set X)

inductive Bad : Type 1
| mk : (∀ X : Type 0, F X) → Bad

def decomp : Bad → (∀ X : Type 0, F X)
| Bad.mk f => f
