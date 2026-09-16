import FormalConjectures.Util.ProblemImports

open Nat Finset

def A268197 (n : ℕ) : ℕ :=
  let is_square_check (m : ℕ) : Prop := (Nat.sqrt m) * (Nat.sqrt m) = m
  let B : ℕ := n + 1
  (Finset.range B).sum fun w =>
  (Finset.range B).sum fun x =>
  (Finset.range B).sum fun y =>
  (Finset.range B).sum fun z =>
    if w > 0 ∧ w^2 + x^2 + y^2 + z^2 = n ∧ is_square_check (w * (25 * w + 24 * x + 48 * y + 96 * z)) then 1 else 0

theorem oeis_268197_conjecture_i :
  (∀ n : ℕ, n > 0 → A268197 n > 0) ∧
  (∀ n : ℕ, A268197 n = 1 ↔
    n = 3 ∨ n = 7 ∨ n = 15 ∨ n = 23 ∨ n = 43 ∨ n = 55 ∨ n = 463 ∨
    (∃ k : ℕ, n = 4^k * 1 ∨ n = 4^k * 31 ∨ n = 4^k * 34)) :=
by
  sorry

theorem oeis_268197_conjecture_i.disproof : ¬ (type_of% @oeis_268197_conjecture_i) := by
  intro h
  have h1 : 12 = 3 ∨ 12 = 7 ∨ 12 = 15 ∨ 12 = 23 ∨ 12 = 43 ∨ 12 = 55 ∨ 12 = 463 ∨
    (∃ k : ℕ, 12 = 4^k * 1 ∨ 12 = 4^k * 31 ∨ 12 = 4^k * 34) := by
    sorry
  have h2 : A268197 12 = 1 := by
    apply (h.right 12).mpr
    exact h1
  sorry
