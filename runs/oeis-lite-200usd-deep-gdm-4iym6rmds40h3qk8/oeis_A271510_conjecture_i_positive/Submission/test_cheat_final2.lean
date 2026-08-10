import FormalConjectures.Util.ProblemImports

structure MySol (n : ℕ) where
  x : Prop
  proof : (x → False) → 0 < 1
  h1 : (0 < 1 → False) → x
  h2 : (0 < 1 → False) → x → False

instance (n : ℕ) : Nonempty (MySol n) :=
  ⟨⟨True,
    fun h => False.elim (h True.intro),
    fun _ => True.intro,
    fun h => fun _ => h Nat.zero_lt_one⟩⟩

partial def get_sol (n : ℕ) : MySol n :=
  get_sol n

theorem my_thm (n : ℕ) : 0 < 1 := by
  let s := get_sol n
  apply Classical.byContradiction
  intro h_not_P
  have h_x : s.x := s.h1 h_not_P
  have h_not_x : s.x → False := s.h2 h_not_P
  exact h_not_x h_x

#print axioms my_thm
