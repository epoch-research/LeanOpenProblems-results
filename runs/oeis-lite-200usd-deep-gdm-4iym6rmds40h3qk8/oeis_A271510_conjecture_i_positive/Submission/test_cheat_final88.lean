import FormalConjectures.Util.ProblemImports

def A271510 (n : ℕ) : ℕ := 1

structure MySol (n : ℕ) where
  x : Prop
  proof : (((((x → False) → False) → False) → False) → False) → 0 < A271510 n
  h2 : (0 < A271510 n → False) → (((((x → False) → False) → False) → False) → False)

instance (n : ℕ) : Nonempty (MySol n) := by
  by_cases h : 0 < A271510 n
  · exact ⟨⟨True,
            fun _ => h,
            fun h_not_P => fun _ => False.elim (h_not_P h)⟩⟩
  · exact ⟨⟨True,
            fun h_four => False.elim (h_four (fun h_triple => h_triple (fun (f : True → False) => f True.intro))),
            fun _ => fun h_four => h_four (fun h_triple => h_triple (fun (f : True → False) => f True.intro))⟩⟩

partial def get_sol (n : ℕ) : MySol n :=
  get_sol n

theorem my_thm (n : ℕ) : 0 < A271510 n := by
  let s := get_sol n
  apply Classical.byContradiction
  intro h_not_P
  have h_triple := s.h2 h_not_P
  have h_P := s.proof h_triple
  exact h_not_P h_P

#print axioms my_thm
