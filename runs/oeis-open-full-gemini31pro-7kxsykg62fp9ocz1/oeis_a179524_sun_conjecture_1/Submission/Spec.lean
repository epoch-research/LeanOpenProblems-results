import FormalConjectures.Util.ProblemImports

open Nat Finset Int

/--
A179524: $a(n) = \sum_{k=0}^n (-4)^k \binom{n}{k}^2 \binom{n-k}{k}^2$.
-/
def a (n : ℕ) : ℤ :=
  (Finset.range (n + 1)).sum fun k : ℕ =>
    (-4 : ℤ) ^ k * (choose n k : ℤ) ^ 2 * (choose (n - k) k : ℤ) ^ 2

/-- Predicate for $n = x^2 + 5y^2$ for $x, y \in \mathbb{Z}$. -/
def is_rep_quadratic_form_5 (n : ℤ) : Prop :=
  ∃ x y : ℤ, n = x^2 + 5 * y^2

theorem oeis_a179524_sun_conjecture_1 (p : ℕ) (hp : Nat.Prime p) :
  let pZ : ℤ := p
  -- The prime 2 and 5 are excluded by the modulo 20 conditions.
  p ≠ 2 ∧ p ≠ 5 →
  let S : ℤ := (Finset.range p).sum fun k => a k
  ( (pZ ≡ 1 [ZMOD 20] ∨ pZ ≡ 9 [ZMOD 20]) →
    (∀ {x y : ℤ}, (is_rep_quadratic_form_5 pZ → S ≡ 4 * x ^ 2 - 2 * pZ [ZMOD pZ ^ 2])) )
  ∧
  ( (pZ ≡ 3 [ZMOD 20] ∨ pZ ≡ 7 [ZMOD 20]) →
    (∀ {x y : ℤ}, (is_rep_quadratic_form_5 (2 * pZ) → S ≡ 2 * x ^ 2 - 2 * pZ [ZMOD pZ ^ 2])) )
  ∧
  ( (pZ ≡ 11 [ZMOD 20] ∨ pZ ≡ 13 [ZMOD 20] ∨ pZ ≡ 17 [ZMOD 20] ∨ pZ ≡ 19 [ZMOD 20]) →
    S ≡ 0 [ZMOD pZ ^ 2] )
  := by sorry

theorem oeis_a179524_sun_conjecture_1.disproof : ¬ (type_of% @oeis_a179524_sun_conjecture_1) := by
  intro h
  have h29 := h 29 (by norm_num)
  dsimp at h29
  have hp : 29 ≠ 2 ∧ 29 ≠ 5 := by norm_num
  have h_cases := h29 hp
  rcases h_cases with ⟨h1, h2, h3⟩
  have h_mod : (29 : ℤ) ≡ 9 [ZMOD 20] := by rfl
  have h_rep : is_rep_quadratic_form_5 29 := ⟨3, 2, by rfl⟩
  have hx0 := @h1 (Or.inr h_mod) 0 0 h_rep
  have hx1 := @h1 (Or.inr h_mod) 1 0 h_rep
  have h_trans := hx1.symm.trans hx0
  have h_diff : (4 * (1 : ℤ) ^ 2 - 58) - (4 * (0 : ℤ) ^ 2 - 58) = 4 := by norm_num
  have h_cong : 4 ≡ 0 [ZMOD 841] := by
    calc (4 : ℤ)
      _ = (4 * 1 ^ 2 - 58) - (4 * 0 ^ 2 - 58) := h_diff.symm
      _ ≡ (4 * 0 ^ 2 - 58) - (4 * 0 ^ 2 - 58) [ZMOD 841] := Int.ModEq.sub_right _ h_trans
      _ = 0 := sub_self _
  have h_false : ¬ ((4 : ℤ) ≡ 0 [ZMOD 841]) := by norm_num
  exact h_false h_cong
