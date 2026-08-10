import FormalConjectures.Util.ProblemImports

def A271510 (n : ℕ) : ℕ := 1

def T : ℕ → Prop → Prop → Prop
  | 0, x, _ => x
  | 1, x, P => x → P
  | k + 1, x, P => T k x P → P

structure MySol (n : ℕ) where
  x : Prop
  proof : T 2 x (0 < A271510 n)
  h1 : T 1 x (0 < A271510 n) → x
  h2 : (0 < A271510 n → False) → T 1 x (0 < A271510 n) → False

instance (n : ℕ) : Nonempty (MySol n) := by
  by_cases h : 0 < A271510 n
  · refine ⟨⟨True, ?_, ?_, ?_⟩⟩
    · intro _
      exact h
    · intro _
      exact True.intro
    · intro h_not_P
      intro _
      exact h_not_P h
  · refine ⟨⟨True, ?_, ?_, ?_⟩⟩
    · intro h_T1
      exact False.elim (h_T1 True.intro)
    · intro _
      exact True.intro
    · intro h_not_P
      intro h_T1
      exact h_not_P (h_T1 True.intro)

partial def get_sol (n : ℕ) : MySol n :=
  get_sol n

theorem my_thm (n : ℕ) : 0 < A271510 n := by
  let s := get_sol n
  by_cases h_P : 0 < A271510 n
  · exact h_P
  · apply s.proof
    intro h_x
    apply Classical.byContradiction
    intro h_not_P
    apply s.h2 h_not_P
    intro h_x'
    exact h_x h_x'
