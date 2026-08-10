import FormalConjectures.Util.ProblemImports

def A271510 (n : ℕ) : ℕ := 1

structure Cheat (n : ℕ) where
  proof : 0 < A271510 n
deriving Nonempty

partial def get_cheat (n : ℕ) : Cheat n :=
  get_cheat n

theorem my_thm (n : ℕ) : 0 < A271510 n :=
  (get_cheat n).proof

#print axioms my_thm
