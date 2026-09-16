import FormalConjectures.Util.ProblemImports
import Submission.Spec

open Nat Finset Int

theorem test : ¬ (∀ (p : ℕ) (hp : Nat.Prime p),
  let pZ : ℤ := p
  p ≠ 2 ∧ p ≠ 5 →
  let S : ℤ := (Finset.range p).sum fun k => a k
  ( (pZ ≡ 1 [ZMOD 20] ∨ pZ ≡ 9 [ZMOD 20]) →
    (∀ {x y : ℤ}, (is_rep_quadratic_form_5 pZ → S ≡ 4 * x ^ 2 - 2 * pZ [ZMOD pZ ^ 2])) )
  ∧
  ( (pZ ≡ 3 [ZMOD 20] ∨ pZ ≡ 7 [ZMOD 20]) →
    (∀ {x y : ℤ}, (is_rep_quadratic_form_5 (2 * pZ) → S ≡ 2 * x ^ 2 - 2 * pZ [ZMOD pZ ^ 2])) )
  ∧
  ( (pZ ≡ 11 [ZMOD 20] ∨ pZ ≡ 13 [ZMOD 20] ∨ pZ ≡ 17 [ZMOD 20] ∨ pZ ≡ 19 [ZMOD 20]) →
    S ≡ 0 [ZMOD pZ ^ 2] )) := by
  intro h
  have h29 := h 29 (by norm_num)
  dsimp at h29
  have hp : 29 ≠ 2 ∧ 29 ≠ 5 := by norm_num
  have h_cases := h29 hp
  rcases h_cases with ⟨h1, h2, h3⟩
  have h_mod : (29 : ℤ) ≡ 9 [ZMOD 20] := by rfl
  have h_imp := h1 (Or.inr h_mod)
  have h_rep : is_rep_quadratic_form_5 29 := ⟨3, 2, by rfl⟩
  have hx0 := @h_imp 0 0 h_rep
  have hx1 := @h_imp 1 0 h_rep
  sorry

