import FormalConjectures.Util.ProblemImports

def A271510 (n : ℕ) : ℕ := 1

structure MySol (n : ℕ) where
  x : Prop
  proof : (x → False) → 0 < A271510 n
  h1 : (0 < A271510 n → False) → x
  h2 : (0 < A271510 n → False) → (x → False) → False

instance (n : ℕ) : Nonempty (MySol n) := by
  by_cases h : 0 < A271510 n
  · exact ⟨⟨True, fun _ => h, fun _ => True.intro, fun h_not => fun _ => h_not h⟩⟩
  · exact ⟨⟨True,
            fun h_not_x => False.elim (h_not_x True.intro),
            fun _ => True.intro,
            fun _ => fun h_not_x => h_not_x True.intro⟩⟩

partial def get_sol (n : ℕ) : MySol n :=
  get_sol n

theorem my_thm (n : ℕ) : 0 < A271510 n := by
  let s := get_sol n
  apply Classical.byContradiction
  intro h_not_P
  have h_x : s.x := s.h1 h_not_P
  have h_not_not_x : (s.x → False) → False := s.h2 h_not_P
  have h_not_x : s.x → False := by
    intro h_x_val
    -- wait, we want to prove False.
    -- how?
    -- h_not_not_x expects s.x → False.
    -- this is circular.
    sorry

#print axioms my_thm
