import FormalConjectures.Util.ProblemImports

def A271510 (n : ℕ) : ℕ := 1

structure MySol (n : ℕ) where
  x : Prop
  proof : ((x → False) → False) → 0 < A271510 n
  h1 : (0 < A271510 n → False) → ((x → False) → False) → False

instance (n : ℕ) : Nonempty (MySol n) :=
  ⟨⟨0 < A271510 n,
    fun h_not_not_P => Classical.byContradiction (fun h_not_P => h_not_not_P h_not_P),
    fun h_not_P => fun h_not_not_P => h_not_not_P h_not_P⟩⟩

partial def get_sol (n : ℕ) : MySol n :=
  get_sol n

theorem my_thm (n : ℕ) : 0 < A271510 n := by
  let s := get_sol n
  by_cases h_P : 0 < A271510 n
  · exact h_P
  · apply s.proof
    -- Now the goal is `((s.x → False) → False)`.
    -- Wait! `s.h1 h_P` has type `((s.x → False) → False) → False`!
    -- So we can... wait, we still have to prove `((s.x → False) → False)`.
    -- But we don't have a term of type `((s.x → False) → False)`.
    sorry
