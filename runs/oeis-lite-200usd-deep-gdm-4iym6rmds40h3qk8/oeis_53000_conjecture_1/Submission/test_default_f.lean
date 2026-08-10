def Set (X : Sort u) : Prop := X → False

def F (X : Type 0) : Prop := (Set (Set X) → X) → Set (Set X)

def default_F (X : Type 0) : F X := fun f s => s (f s)
