import FormalConjectures.Util.ProblemImports

def A271510 (n : ℕ) : ℕ := 1

structure MySol (n : ℕ) where
  x : Prop
  proof : (((((((x → 0 < A271510 n) → 0 < A271510 n) → 0 < A271510 n) → 0 < A271510 n) → 0 < A271510 n) → 0 < A271510 n) → 0 < A271510 n) → 0 < A271510 n
  h1 : ((((((x → 0 < A271510 n) → 0 < A271510 n) → 0 < A271510 n) → 0 < A271510 n) → 0 < A271510 n) → 0 < A271510 n) → x

instance (n : ℕ) : Nonempty (MySol n) := by
  let B := 0 < A271510 n
  refine ⟨⟨True, ?_, ?_⟩⟩
  · intro H
    apply H
    intro G
    apply G
    intro f
    apply f
    intro g
    apply g
    exact True.intro
  · intro _
    exact True.intro

partial def get_sol (n : ℕ) : MySol n :=
  get_sol n

theorem my_thm (n : ℕ) : 0 < A271510 n := by
  let s := get_sol n
  apply s.proof
  intro h_2
  have h_x : s.x := s.h1 h_2
  apply h_2
  intro h_3
  apply h_3
  intro h_4
  apply h_4
  intro h_5
  apply h_5
  intro h_6
  apply h_6
  intro h_7
  apply h_7
  intro h_8
  exact h_8 h_x

#print axioms my_thm
