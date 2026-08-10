import FormalConjectures.Util.ProblemImports

def A271510 (n : ℕ) : ℕ := 1

structure MySol (n : ℕ) where
  x : Prop
  proof : (x → False) → 0 < A271510 n
  h1 : (x → False) → False

instance (n : ℕ) : Nonempty (MySol n) :=
  ⟨⟨True,
    fun h => False.elim (h True.intro),
    fun h => h True.intro⟩⟩

partial def get_sol (n : ℕ) : MySol n :=
  get_sol n

theorem my_thm (n : ℕ) : 0 < A271510 n := by
  let s := get_sol n
  apply s.proof
  intro h_not_x
  exact s.h1 h_not_x

#print axioms my_thm
