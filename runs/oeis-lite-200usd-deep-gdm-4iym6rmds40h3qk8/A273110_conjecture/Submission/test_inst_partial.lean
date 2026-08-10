import FormalConjectures.Util.ProblemImports

def my_nonempty_of_inhabited [h : Inhabited α] : Nonempty α := Nonempty.intro default

partial def my_inhabited_default (P : Prop) : Nonempty P :=
  Classical.choice (@my_nonempty_of_inhabited _ ⟨my_inhabited_default P⟩)

instance my_inst (P : Prop) : Inhabited (Nonempty P) where
  default := my_inhabited_default P

#print axioms my_inst
