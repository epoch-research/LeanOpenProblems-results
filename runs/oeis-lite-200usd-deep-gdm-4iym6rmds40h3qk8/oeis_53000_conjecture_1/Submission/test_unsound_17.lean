def Set (X : Sort u) : Sort (max u 1) := X → Prop

def F (X : Sort u) : Sort (max u 1) := (Set (Set X) → X) → Set (Set X)

inductive Unsound : Prop
| mk : (∀ X : Sort u, F X) → Unsound
| base : Unsound

abbrev U := Unsound

def decomp : U → (∀ X : Sort u, F X)
| Unsound.base => fun _ => sorry
| Unsound.mk f => f
