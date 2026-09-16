import Submission.Spec
open Nat Finset ZMod

instance hp13 : Fact (Nat.Prime 13) := ⟨by decide⟩

lemma disproof_lemma : ¬ (type_of% @oeis_A336982_conjecture_3) := by
  intro h
  have h13 := h 13 (by decide)
  rcases h13 with ⟨_, _, h3, _, _⟩
  
  have hl : legendreSym 13 3 = 1 ∧ legendreSym 13 2 = -1 ∧ legendreSym 13 5 = -1 := by decide
  have hex : ∃ x y : ℤ, (13 : ℤ) = 3 * x^2 + 10 * y^2 := ⟨1, 1, by decide⟩
  
  have h3_eval := h3 hl hex
  rcases h3_eval with ⟨x, y, heq, hS⟩
  
  have hx2 : x^2 = 1 := by
    have hx_pos : x^2 ≥ 0 := sq_nonneg x
    have hy_pos : y^2 ≥ 0 := sq_nonneg y
    omega
  
  rw [hx2] at hS
  have hS_eq : S_sum 13 % (13^2) = (legendreSym 13 (-1 : ℤ) * (2 * (13 : ℤ) - 12 * 1)) % (13^2) := hS
  have h1 : S_sum 13 % (13^2) = 138 := by decide
  have h2 : (legendreSym 13 (-1 : ℤ) * (2 * (13 : ℤ) - 12 * 1)) % (13^2) = 14 := by decide
  rw [h1, h2] at hS_eq
  revert hS_eq
  decide
