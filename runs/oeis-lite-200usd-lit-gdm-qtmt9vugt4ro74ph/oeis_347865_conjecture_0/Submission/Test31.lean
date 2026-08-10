import FormalConjectures.Util.ProblemImports

partial def my_fun (A : Type) (x : Unit) : A :=
  my_fun A x

theorem tail_pos (n : Nat) : a n > 0 :=
  (my_fun (PLift (a n > 0)) ()).down
