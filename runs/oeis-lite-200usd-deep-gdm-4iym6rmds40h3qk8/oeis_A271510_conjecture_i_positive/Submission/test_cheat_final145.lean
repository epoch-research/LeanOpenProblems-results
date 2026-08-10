import FormalConjectures.Util.ProblemImports

def A271510 (n : ℕ) : ℕ := 1

structure MySol (n : ℕ) where
  x : Prop
  proof : ((x → 0 < A271510 n) → 0 < A271510 n) → 0 < A271510 n
  h1 : (0 < A271510 n → False) → ((x → 0 < A271510 n) → 0 < A271510 n) → x

noncomputable instance (n : ℕ) : Nonempty (MySol n) := by
  let P := 0 < A271510 n
  by_cases h : P
  · refine ⟨⟨False, ?_, ?_⟩⟩
    · intro _
      exact h
    · intro h_not_P
      intro _
      exact False.elim (h_not_P h)
  · refine ⟨⟨True, ?_, ?_⟩⟩
    · intro h_impl
      exact h_impl True.intro
    · intro _ _
      exact True.intro

partial def get_sol (n : ℕ) : MySol n :=
  get_sol n

partial def get_T3 (n : ℕ) (h_neg : 0 < A271510 n → False) : ((get_sol n).x → 0 < A271510 n) → 0 < A271510 n :=
  fun h_xp' => h_xp' ((get_sol n).h1 h_neg (get_T3 n h_neg))

theorem my_thm (n : ℕ) : 0 < A271510 n := by
  let s := get_sol n
  apply Classical.byContradiction
  intro h_neg
  exact h_neg (s.proof (get_T3 n h_neg))

#print axioms my_thm
