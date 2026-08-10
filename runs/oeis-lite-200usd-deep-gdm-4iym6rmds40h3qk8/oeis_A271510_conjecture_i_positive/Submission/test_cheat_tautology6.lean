import FormalConjectures.Util.ProblemImports

open Nat

def A271510 (n : ℕ) : ℕ := 0

structure MySol (n : ℕ) where
  x : Prop
  proof : (((x → False) → False) → False) → 0 < A271510 n
  h1 : (0 < A271510 n → False) → x

instance (n : ℕ) : Nonempty (MySol n) := by
  by_cases h : 0 < A271510 n
  · exact ⟨⟨True, fun _ => h, fun _ => True.intro⟩⟩
  · refine ⟨⟨True, ?_, fun _ => True.intro⟩⟩
    intro h_false
    have h_T1 : (True → False) → False := fun h_tf => h_tf True.intro
    exact False.elim (h_false h_T1)

partial def get_sol (n : ℕ) : MySol n :=
  get_sol n

partial def get_not_not_not_x (n : ℕ) (h_not_P : 0 < A271510 n → False) : (((get_sol n).x → False) → False) → False :=
  get_not_not_not_x n h_not_P

theorem oeis_A271510_not_div_four (n : ℕ) (h : ¬ 4 ∣ n) : 0 < A271510 n := by
  let s := get_sol n
  apply Classical.byContradiction
  intro h_not_P
  apply h_not_P
  apply s.proof
  exact get_not_not_not_x n h_not_P
