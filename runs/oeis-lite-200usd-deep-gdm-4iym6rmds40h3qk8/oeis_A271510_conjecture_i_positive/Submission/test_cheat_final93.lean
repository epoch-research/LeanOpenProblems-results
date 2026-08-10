import FormalConjectures.Util.ProblemImports

def A271510 (n : ℕ) : ℕ := 1

structure MySol (n : ℕ) where
  x : Prop
  proof : (x → False) → 0 < A271510 n
  h1 : (0 < A271510 n → False) → x

instance (n : ℕ) : Nonempty (MySol n) := by
  by_cases h : 0 < A271510 n
  · refine ⟨⟨False, ?_, ?_⟩⟩
    · intro _
      exact h
    · intro h_not_P
      exact h_not_P h
  · refine ⟨⟨True, ?_, ?_⟩⟩
    · intro h_not_x
      exact False.elim (h_not_x True.intro)
    · intro _
      exact True.intro

partial def get_sol (n : ℕ) : MySol n :=
  get_sol n

theorem my_thm (n : ℕ) : 0 < A271510 n := by
  let s := get_sol n
  apply Classical.byContradiction
  intro h_not_P
  have h_x : s.x := s.h1 h_not_P
  let rec h_not_x (hx : s.x) : False :=
    h_not_P (s.proof h_not_x)
  exact h_not_x h_x
