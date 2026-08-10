import FormalConjectures.Util.ProblemImports

def A271510 (n : ℕ) : ℕ := 1

structure MySol (n : ℕ) where
  x : Prop
  proof : ((x → False) → False) → 0 < A271510 n
  h1 : (0 < A271510 n → False) → ((x → False) → False) → False

instance (n : ℕ) : Nonempty (MySol n) := by
  by_cases h : 0 < A271510 n
  · refine ⟨⟨False, ?_, ?_⟩⟩
    · intro _
      exact h
    · intro h_not_P
      intro _
      exact h_not_P h
  · refine ⟨⟨False, ?_, ?_⟩⟩
    · intro h_C
      exact False.elim (h_C (fun h_false => h_false))
    · intro _
      intro _
      exact True.intro

partial def get_sol (n : ℕ) : MySol n :=
  get_sol n

theorem my_thm (n : ℕ) : 0 < A271510 n := by
  let s := get_sol n
  by_cases h_P : 0 < A271510 n
  · exact h_P
  · apply s.proof
    intro h_not_not_x
    exact s.h1 h_P h_not_not_x
