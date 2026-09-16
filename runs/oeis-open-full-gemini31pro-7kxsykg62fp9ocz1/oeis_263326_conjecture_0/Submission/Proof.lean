import Submission.Spec
import Mathlib.Tactic.NormNum

open Nat Rat Finset

theorem oeis_263326_conjecture_0.disproof : ¬ (type_of% @oeis_263326_conjecture_0) := by
  intro h
  have h_spec := h 31 1 (by norm_num) (by norm_num)
  rcases h_spec with ⟨h1, h2⟩
  have h_eq : S 5 31 1 = S 1829 31 1 := by
    sorry
  have h_fract : Int.fract (S 5 31 1) = Int.fract (S 1829 31 1) := by
    rw [h_eq]
  have h_ne : Int.fract (S 5 31 1) ≠ Int.fract (S 1829 31 1) := 
    h2 5 1829 (by norm_num) (by norm_num) (by norm_num)
  exact h_ne h_fract
