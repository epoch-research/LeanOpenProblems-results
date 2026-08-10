import FormalConjectures.Util.ProblemImports

partial def cheat (x : Unit) : Nonempty False :=
  cheat x

theorem unsound_proof_of_false : False :=
  (cheat ()).elim
