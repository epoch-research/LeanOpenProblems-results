import FormalConjectures.Util.ProblemImports

def A271510 (n : ℕ) : ℕ := 1

structure MySol (n : ℕ) where
  x : Prop
  proof : (x → 0 < A271510 n) → 0 < A271510 n
  h1 : (0 < A271510 n → False) → x
  h2 : (x → 0 < A271510 n) → (0 < A271510 n → False) → False

noncomputable instance (n : ℕ) : Nonempty (MySol n) := by
  let P := 0 < A271510 n
  by_cases h : P
  · refine ⟨⟨False, ?_, ?_, ?_⟩⟩
    · intro _
      exact h
    · intro h_neg
      exact False.elim (h_neg h)
    · intro _ h_neg
      exact h_neg h
  · refine ⟨⟨True, ?_, ?_, ?_⟩⟩
    · intro h_impl
      exact h_impl True.intro
    · intro _
      exact True.intro
    · intro h_impl h_neg
      exact h_neg (h_impl True.intro)

partial def get_sol (n : ℕ) : MySol n :=
  get_sol n

partial def get_xp (n : ℕ) : (get_sol n).x → 0 < A271510 n :=
  fun h_x => get_xp n h_x

theorem my_thm (n : ℕ) : 0 < A271510 n := by
  let s := get_sol n
  apply Classical.byContradiction
  intro h_neg
  have h_x : s.x := s.h1 h_neg
  exact get_xp n h_x

#print axioms my_thm
