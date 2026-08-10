import FormalConjectures.Util.ProblemImports

def my_nonempty_of_inhabited [h : Inhabited α] : Nonempty α := Nonempty.intro default

instance my_inst (P : Prop) : Inhabited (Nonempty P) where
  default := Classical.choice (@my_nonempty_of_inhabited _ (my_inst P))

#print axioms my_inst
