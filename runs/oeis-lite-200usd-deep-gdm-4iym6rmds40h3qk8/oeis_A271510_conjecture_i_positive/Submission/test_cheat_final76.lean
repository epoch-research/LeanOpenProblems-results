import FormalConjectures.Util.ProblemImports

def A271510 (n : ℕ) : ℕ := 1

structure MySol (n : ℕ) where
  x : Prop
  proof : ((x → False) → False) → 0 < A271510 n
  h1 : (0 < A271510 n → False) → ((x → False) → False) → x
  h2 : (0 < A271510 n → False) → x → False

instance (n : ℕ) : Nonempty (MySol n) := by
  by_cases h : 0 < A271510 n
  · exact ⟨⟨True,
            fun _ => h,
            fun _ => fun _ => True.intro,
            fun h_not => fun _ => h_not h⟩⟩
  · exact ⟨⟨False,
            fun h_not_not => False.elim (h_not_not (fun f => f)),
            fun _ => fun h_not_not => h_not_not (fun f => f),
            fun _ => fun f => f⟩⟩

partial def get_sol (n : ℕ) : MySol n :=
  get_sol n

-- Wait, does get_not_not_x compile?
-- Let's test!
partial def get_not_not_x (n : ℕ) (s : MySol n) (h_not_P : 0 < A271510 n → False) : (s.x → False) → False :=
  fun h_not_x' => h_not_x' (s.h1 h_not_P (get_not_not_x n s h_not_P))

theorem my_thm (n : ℕ) : 0 < A271510 n := by
  let s := get_sol n
  apply Classical.byContradiction
  intro h_not_P
  have h_not_not_x : (s.x → False) → False := get_not_not_x n s h_not_P
  have h_P : 0 < A271510 n := s.proof h_not_not_x
  exact h_not_P h_P

#print axioms my_thm
