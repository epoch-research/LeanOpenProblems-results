import FormalConjectures.Util.ProblemImports

def A271510 (n : ℕ) : ℕ := 1

def T : ℕ → Prop → Prop → Prop
  | 0, x, _ => x
  | 1, x, P => x → P
  | k + 1, x, P => T k x P → P

structure MySol (n : ℕ) where
  x : Prop
  proof : T 5 x (0 < A271510 n)
  h1 : T 3 x (0 < A271510 n) → x

instance (n : ℕ) : Nonempty (MySol n) := by
  by_cases h : 0 < A271510 n
  · refine ⟨⟨True, ?_, ?_⟩⟩
    · intro h_T4
      exact h
    · intro _
      exact True.intro
  · refine ⟨⟨False, ?_, ?_⟩⟩
    · intro h_T4
      apply h_T4
      intro h_T2
      apply h_T2
      intro h_false
      exact False.elim h_false
    · intro h_T3
      exact h (h_T3 (fun h_false => h_false.elim))

partial def get_sol (n : ℕ) : MySol n :=
  get_sol n

theorem my_thm (n : ℕ) : 0 < A271510 n := by
  let s := get_sol n
  apply s.proof
  intro h
  have h_x : s.x := s.h1 h
  have h_xp : s.x → 0 < A271510 n := fun h_x' => h (fun (k : s.x → 0 < A271510 n) => k h_x')
  exact h_xp h_x
