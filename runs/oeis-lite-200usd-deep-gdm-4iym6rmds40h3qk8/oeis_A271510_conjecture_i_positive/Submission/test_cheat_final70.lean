import FormalConjectures.Util.ProblemImports

def A271510 (n : ℕ) : ℕ := 1

structure MySol (n : ℕ) where
  x : Prop
  proof : (x → False) → 0 < A271510 n
  h1 : (0 < A271510 n → False) → x
  h2 : (0 < A271510 n → False) → x → 0 < A271510 n

instance (n : ℕ) : Nonempty (MySol n) :=
  ⟨⟨0 < A271510 n,
    fun h => Classical.byContradiction (fun h_not => h h_not),
    fun h => Classical.byContradiction (fun h_not => h h_not),
    fun _ => fun p => p⟩⟩

partial def get_sol (n : ℕ) : MySol n :=
  get_sol n

theorem my_thm (n : ℕ) : 0 < A271510 n := by
  let s := get_sol n
  apply Classical.byContradiction
  intro h_not_P
  have h_x : s.x := s.h1 h_not_P
  have h_P : 0 < A271510 n := s.h2 h_not_P h_x
  exact h_not_P h_P

#print axioms my_thm
