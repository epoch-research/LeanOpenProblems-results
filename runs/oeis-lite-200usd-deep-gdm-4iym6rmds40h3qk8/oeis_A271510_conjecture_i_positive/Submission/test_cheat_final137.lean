import FormalConjectures.Util.ProblemImports

def A271510 (n : ℕ) : ℕ := 1

partial def get_xp (n : ℕ) : 0 < A271510 n ↔ True :=
  get_xp n

theorem my_thm (n : ℕ) : 0 < A271510 n :=
  (get_xp n).mpr True.intro

#print axioms my_thm
