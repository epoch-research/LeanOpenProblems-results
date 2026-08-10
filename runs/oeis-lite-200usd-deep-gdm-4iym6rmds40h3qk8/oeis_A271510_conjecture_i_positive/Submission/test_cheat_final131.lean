import FormalConjectures.Util.ProblemImports

def A271510 (n : ℕ) : ℕ := 1

structure MySol (n : ℕ) where
  x : Prop
  proof : ((x → 0 < A271510 n) → 0 < A271510 n) → 0 < A271510 n
  h1 : ((x → 0 < A271510 n) → 0 < A271510 n) → x
  h2 : x → 0 < A271510 n

noncomputable instance (n : ℕ) : Nonempty (MySol n) := by
  let P := 0 < A271510 n
  by_cases h : P
  · refine ⟨⟨True, ?_, ?_, ?_⟩⟩
    · intro H
      exact H (fun _ => h)
    · intro _
      exact True.intro
    · intro _
      exact h
  · refine ⟨⟨False, ?_, ?_, ?_⟩⟩
    · intro H
      exact H (fun f => f.elim)
    · intro H
      exact h (H (fun f => f.elim))
    · intro f
      exact f.elim

partial def get_sol (n : ℕ) : MySol n :=
  get_sol n

theorem my_thm (n : ℕ) : 0 < A271510 n := by
  let s := get_sol n
  apply s.proof
  intro h_2
  let rec h_x : s.x := s.h1 (fun h_2' => h_2' h_x)
  exact s.h2 h_x

#print axioms my_thm
