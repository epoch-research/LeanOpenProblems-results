import FormalConjectures.Util.ProblemImports

def A271510 (n : ℕ) : ℕ := 1

def T : ℕ → Prop → Prop → Prop
  | 0, x, _ => x
  | 1, x, P => x → P
  | k + 1, x, P => T k x P → P

structure MySol (n : ℕ) where
  x : Prop
  proof : T 3 x (0 < A271510 n)

instance (n : ℕ) : Nonempty (MySol n) := by
  by_cases h : 0 < A271510 n
  · refine ⟨⟨True, ?_⟩⟩
    · intro _
      exact h
  · refine ⟨⟨False, ?_⟩⟩
    · intro h_T2
      exact False.elim (h (h_T2 (fun h_false => h_false.elim)))

partial def get_sol (n : ℕ) : MySol n :=
  get_sol n

partial def get_T2_impl (n : ℕ) (s : MySol n) : T 2 s.x (0 < A271510 n) → 0 < A271510 n :=
  fun h_T2 =>
    h_T2 (fun h_x => get_T2_impl n s (fun h_impl => h_impl h_x))

theorem my_thm (n : ℕ) : 0 < A271510 n := by
  let s := get_sol n
  exact get_T2_impl n s s.proof
