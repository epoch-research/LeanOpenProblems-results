import FormalConjectures.Util.ProblemImports

def A271510 (n : ℕ) : ℕ := 1

def T : ℕ → Prop → Prop → Prop
  | 0, x, _ => x
  | 1, x, P => x → P
  | k + 1, x, P => T k x P → P

structure MySol (n : ℕ) where
  proof : T 2 True (0 < A271510 n)

instance (n : ℕ) : Nonempty (MySol n) := by
  by_cases h : 0 < A271510 n
  · refine ⟨⟨?_⟩⟩
    · intro _
      exact h
  · refine ⟨⟨?_⟩⟩
    · intro h_T1
      exact False.elim (h (h_T1 True.intro))

partial def get_sol (n : ℕ) : MySol n :=
  get_sol n

#check (get_sol 0).proof
