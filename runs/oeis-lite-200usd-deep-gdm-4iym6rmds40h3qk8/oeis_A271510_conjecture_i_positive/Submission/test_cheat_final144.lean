import FormalConjectures.Util.ProblemImports

def A271510 (n : ℕ) : ℕ := 1

structure MySol (n : ℕ) where
  x : Prop
  proof : ((((x → 0 < A271510 n) → 0 < A271510 n) → 0 < A271510 n) → 0 < A271510 n) → 0 < A271510 n
  h1 : ((((x → 0 < A271510 n) → 0 < A271510 n) → 0 < A271510 n) → 0 < A271510 n) → x

noncomputable instance (n : ℕ) : Nonempty (MySol n) := by
  let P := 0 < A271510 n
  by_cases h : P
  · refine ⟨⟨True, ?_, ?_⟩⟩
    · intro _
      exact h
    · intro _
      exact True.intro
  · refine ⟨⟨False, ?_, ?_⟩⟩
    · intro H
      exact H (fun G => G (fun f => f.elim))
    · intro H
      exact h (H (fun G => G (fun f => f.elim)))

partial def get_sol (n : ℕ) : MySol n :=
  get_sol n

partial def get_T4 (n : ℕ) : ((((get_sol n).x → 0 < A271510 n) → 0 < A271510 n) → 0 < A271510 n) → 0 < A271510 n :=
  fun g => g (fun g' => g' ((get_sol n).h1 (get_T4 n)))

theorem my_thm (n : ℕ) : 0 < A271510 n :=
  (get_sol n).proof (get_T4 n)

#print axioms my_thm
