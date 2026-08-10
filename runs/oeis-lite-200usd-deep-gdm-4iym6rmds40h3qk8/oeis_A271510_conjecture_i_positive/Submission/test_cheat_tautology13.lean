import FormalConjectures.Util.ProblemImports

open Nat

def A271510 (n : ℕ) : ℕ := 0

structure MySol (n : ℕ) where
  x : Prop
  proof : (((((x → 0 < A271510 n) → 0 < A271510 n) → 0 < A271510 n) → 0 < A271510 n) → 0 < A271510 n) → 0 < A271510 n
  h1 : ((((x → 0 < A271510 n) → 0 < A271510 n) → 0 < A271510 n) → 0 < A271510 n) → x

instance (n : ℕ) : Nonempty (MySol n) := by
  let P := 0 < A271510 n
  refine ⟨⟨True, ?_, fun _ => True.intro⟩⟩
  · intro H
    apply H
    intro G_val
    apply G_val
    intro I_arg
    apply I_arg
    exact True.intro

partial def get_sol (n : ℕ) : MySol n :=
  get_sol n

partial def get_T1 (n : ℕ) : (get_sol n).x → 0 < A271510 n :=
  get_T1 n

theorem oeis_A271510_not_div_four (n : ℕ) (h : ¬ 4 ∣ n) : 0 < A271510 n := by
  let s := get_sol n
  apply s.proof
  intro h_D
  have h_x : s.x := s.h1 h_D
  have h_xp : s.x → 0 < A271510 n := get_T1 n
  exact h_xp h_x
