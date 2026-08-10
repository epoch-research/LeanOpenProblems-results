import FormalConjectures.Util.ProblemImports

structure MySol (n : ℕ) where
  x : Prop
  proof : (((x → False) → False) → False) → 0 < 1
  h1 : 0 < 1 → x

instance (n : ℕ) : Nonempty (MySol n) := by
  constructor
  refine ⟨(0 < 1 → False) → False, ?_, ?_⟩
  · intro h
    apply Classical.byContradiction
    intro h_not_p
    apply h
    intro h_not_not_p
    exact h_not_not_p h_not_p
  · intro h_pos
    intro h_not_p
    exact h_not_p h_pos

partial def get_sol (n : ℕ) : MySol n :=
  get_sol n

theorem my_thm (n : ℕ) : 0 < 1 := by
  let s := get_sol n
  apply s.proof
  intro h_not_not_not_x
  exact h_not_not_not_x (fun h_not_x => h_not_x (s.h1 (s.proof (fun h_not_not_not_x' => h_not_x (s.h1 (s.proof h_not_not_not_x'))))))
























#print axioms my_thm





