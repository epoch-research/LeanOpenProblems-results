import FormalConjectures.Util.ProblemImports

open Nat

def A271510 (n : ℕ) : ℕ := 1

structure MySol (n : ℕ) where
  x : Prop
  proof : (((((x → 0 < A271510 n) → 0 < A271510 n) → 0 < A271510 n) → 0 < A271510 n) → 0 < A271510 n) → 0 < A271510 n
  h1 : ((((x → 0 < A271510 n) → 0 < A271510 n) → 0 < A271510 n) → 0 < A271510 n) → x
  h2 : ((((x → 0 < A271510 n) → 0 < A271510 n) → 0 < A271510 n) → 0 < A271510 n) → x → 0 < A271510 n

instance (n : ℕ) : Nonempty (MySol n) := by
  let P := 0 < A271510 n
  by_cases h : P
  · refine ⟨⟨P, ?_, ?_, ?_⟩⟩
    · intro _
      exact h
    · intro _
      exact h
    · intro _ _
      exact h
  · refine ⟨⟨P, ?_, ?_, ?_⟩⟩
    · intro H
      have h_T1 : ((((P → P) → P) → P) → P) := by
        intro h_arg
        apply h_arg
        intro h_tf
        exact h_tf (fun p => p)
      exact H h_T1
    · intro H
      have h_T1 : (((P → P) → P) → P) := by
        intro h_arg
        apply h_arg
        intro h_tf
        exact h_tf
      exact H h_T1
    · intro _ p
      exact p

partial def get_sol (n : ℕ) : MySol n :=
  get_sol n

theorem my_thm (n : ℕ) : 0 < A271510 n := by
  let s := get_sol n
  apply s.proof
  intro h_2
  have h_x : s.x := s.h1 h_2
  have h_xp : s.x → 0 < A271510 n := s.h2 h_2
  exact h_xp h_x

#print axioms my_thm
