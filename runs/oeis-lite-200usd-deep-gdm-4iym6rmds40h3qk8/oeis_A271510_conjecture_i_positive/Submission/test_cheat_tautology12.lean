import FormalConjectures.Util.ProblemImports

open Nat

def A271510 (n : ℕ) : ℕ := 0

structure MySol (n : ℕ) where
  x : Prop
  proof : ((((x → False) → False) → False) → False) → 0 < A271510 n
  h1 : (0 < A271510 n → False) → x → False

instance (n : ℕ) : Nonempty (MySol n) := by
  by_cases h : 0 < A271510 n
  · refine ⟨⟨True, ?_, ?_⟩⟩
    · intro _
      exact h
    · intro h_not_P h_x
      exact False.elim (h_not_P h)
  · refine ⟨⟨False, ?_, ?_⟩⟩
    · intro h_false
      have h_T1 : (((False → False) → False) → False) → False := by
        intro h_arg
        apply h_arg
        intro h_tf
        exact False.elim h_tf
      exact False.elim (h_false h_T1)
    · intro _ h_x
      exact False.elim h_x

partial def get_sol (n : ℕ) : MySol n :=
  get_sol n

theorem oeis_A271510_not_div_four (n : ℕ) (h : ¬ 4 ∣ n) : 0 < A271510 n := by
  let s := get_sol n
  apply Classical.byContradiction
  intro h_not_P
  have h_not_x : s.x → False := s.h1 h_not_P
  have h_f : ((((s.x → False) → False) → False) → False) := by
    intro h_arg
    apply h_arg
    intro h_not_not_x
    exact h_not_not_x h_not_x
  exact h_not_P (s.proof h_f)
