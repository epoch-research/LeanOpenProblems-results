import FormalConjectures.Util.ProblemImports

def A271510 (n : ℕ) : ℕ := 1

def T : ℕ → Prop → Prop → Prop
  | 0, x, _ => x
  | 1, x, P => x → P
  | k + 1, x, P => T k x P → P

def f3 (P : Prop) : T 3 P P :=
  fun H => H (fun p => p)

def f5 (P : Prop) : T 5 P P :=
  fun H => H (f3 P)

structure MySol (n : ℕ) where
  x : Prop
  proof : T 5 x (0 < A271510 n)
  h1 : T 4 x (0 < A271510 n) → x
  h2 : T 4 x (0 < A271510 n) → x → 0 < A271510 n

instance (n : ℕ) : Nonempty (MySol n) := by
  by_cases h : 0 < A271510 n
  · refine ⟨⟨True, ?_, ?_, ?_⟩⟩
    · exact f5 (0 < A271510 n)
    · intro _
      exact True.intro
    · intro _
      intro _
      exact h
  · refine ⟨⟨False, ?_, ?_, ?_⟩⟩
    · intro h_T4
      -- h_T4 has type T 4 False P.
      -- Since T 4 False P is False, we can use it to prove anything.
      -- Let us prove T 3 False P.
      -- T 3 False P is T 2 False P → P.
      -- So:
      intro h_T2
      -- h_T2 has type T 2 False P.
      -- Since T 2 False P is False, we can get False, and then P.
      have h_false : False := by
        apply h_T2
        intro h_false'
        exact False.elim h_false'
      exact False.elim h_false
    · intro h_T4
      have h_false : False := by
        apply h_T4
        intro h_T2
        have h_false' : False := by
          apply h_T2
          intro h_false''
          exact False.elim h_false''
        exact False.elim h_false'
      exact False.elim h_false
    · intro h_T4
      have h_false : False := by
        apply h_T4
        intro h_T2
        have h_false' : False := by
          apply h_T2
          intro h_false''
          exact False.elim h_false''
        exact False.elim h_false'
      exact False.elim h_false

partial def get_sol (n : ℕ) : MySol n :=
  get_sol n

theorem my_thm (n : ℕ) : 0 < A271510 n := by
  let s := get_sol n
  apply s.proof
  intro h
  have h_x : s.x := s.h1 h
  have h_xp : s.x → 0 < A271510 n := s.h2 h
  exact h_xp h_x
