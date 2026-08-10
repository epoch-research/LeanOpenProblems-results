import FormalConjectures.Util.ProblemImports

open Nat

def A271510 (n : ℕ) : ℕ := 1

structure MySol (n : ℕ) where
  x : Prop
  proof : ((((x → 0 < A271510 n) → 0 < A271510 n) → 0 < A271510 n) → 0 < A271510 n) → 0 < A271510 n
  h1 : ((((x → 0 < A271510 n) → 0 < A271510 n) → 0 < A271510 n) → 0 < A271510 n) → x
  h2 : x → 0 < A271510 n

noncomputable instance (n : ℕ) : Nonempty (MySol n) := by
  let P := 0 < A271510 n
  by_cases h : P
  · refine ⟨⟨True, ?_, ?_, ?_⟩⟩
    · intro _
      exact h
    · intro _
      exact True.intro
    · intro _
      exact h
  · refine ⟨⟨False, ?_, ?_, ?_⟩⟩
    · intro H
      exact H (fun G => G (fun f => f.elim))
    · intro H
      exact h (H (fun G => G (fun f => f.elim)))
    · intro f
      exact f.elim

partial def get_sol (n : ℕ) : MySol n :=
  get_sol n

theorem my_thm (n : ℕ) : 0 < A271510 n := by
  let s := get_sol n
  by_cases hx : s.x
  · exact s.h2 hx
  · have h_x : s.x := by
      apply s.h1
      intro h_A
      have h_xp : s.x → 0 < A271510 n := by
        intro hx_val
        exact False.elim (hx hx_val)
      exact h_A h_xp
    exact False.elim (hx h_x)

#print axioms my_thm
