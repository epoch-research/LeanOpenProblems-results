import FormalConjectures.Util.ProblemImports

partial def my_unsafe_fun (n : Nat) : Nat :=
  my_unsafe_fun n

theorem my_thm (n : Nat) : my_unsafe_fun n = my_unsafe_fun n := by
  rfl

#print axioms my_thm
