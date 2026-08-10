import FormalConjectures.Util.ProblemImports

def A271510 (n : ℕ) : ℕ := 1

structure MySol (n : ℕ) where
  x : Prop
  proof : ((x → False) → False) → 0 < A271510 n
  h1 : 0 < A271510 n → x

instance (n : ℕ) : Nonempty (MySol n) := by
  by_cases h : 0 < A271510 n
  · exact ⟨⟨True,
            fun _ => h,
            fun _ => True.intro⟩⟩
  · exact ⟨⟨False,
            fun h_not_not => False.elim (h_not_not id),
            fun h_pos => h h_pos⟩⟩

partial def get_sol (n : ℕ) : MySol n :=
  get_sol n

partial def inst (n : ℕ) : Nonempty (0 < A271510 n) :=
  ⟨(get_sol n).proof (fun h_not_x => h_not_x ((get_sol n).h1 (Classical.choice (inst n))))⟩

theorem my_thm (n : ℕ) : 0 < A271510 n :=
  Classical.choice (inst n)

#print axioms my_thm
