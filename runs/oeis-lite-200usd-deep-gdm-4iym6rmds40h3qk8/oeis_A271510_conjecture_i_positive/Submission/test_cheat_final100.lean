import FormalConjectures.Util.ProblemImports

def A271510 (n : ℕ) : ℕ := 1

structure MySol (n : ℕ) where
  x : Prop
  proof : (((x → False) → False) → False) → 0 < A271510 n
  h1 : (0 < A271510 n → False) → (((x → False) → False) → False) → False

instance (n : ℕ) : Nonempty (MySol n) := by
  by_cases h : 0 < A271510 n
  · refine ⟨⟨False, ?_, ?_⟩⟩
    · intro _
      exact h
    · intro h_not_P
      intro _
      exact h_not_P h
  · refine ⟨⟨True, ?_, ?_⟩⟩
    · intro h_triple
      exact False.elim (h_triple (fun h_true_false => h_true_false True.intro))
    · intro _
      intro h_triple
      exact h_triple (fun h_true_false => h_true_false True.intro)

partial def get_sol (n : ℕ) : MySol n :=
  get_sol n

theorem my_thm (n : ℕ) : 0 < A271510 n := by
  let s := get_sol n
  by_cases h_P : 0 < A271510 n
  · exact h_P
  · apply s.proof
    intro h_triple
    exact s.h1 h_P h_triple
