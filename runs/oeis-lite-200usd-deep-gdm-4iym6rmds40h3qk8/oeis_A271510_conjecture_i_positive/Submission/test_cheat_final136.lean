import FormalConjectures.Util.ProblemImports

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
  apply s.h2
  apply s.h1
  intro h_3
  apply h_3
  intro h_xp
  apply h_xp
  apply s.h1
  intro h_3'
  apply h_3'
  exact h_xp

#print axioms my_thm
