import FormalConjectures.Util.ProblemImports

open Nat Finset

def a (n : ℕ) : ℕ :=
  let is_perfect_square (m : ℕ) : Prop := (Nat.sqrt m) ^ 2 = m
  let max_sq_term_root := Nat.sqrt n + 1
  let max_quad_term_root := Nat.sqrt (Nat.sqrt n) + 1
  Finset.sum (range max_quad_term_root) fun z =>
    Finset.sum (range max_quad_term_root) fun y =>
      Finset.sum (range max_sq_term_root) fun x =>
        let rest : ℕ := 2 * x^2 + y^4 + 3 * z^4
        if h : rest ≤ n then
          if is_perfect_square (n - rest) then 1 else 0
        else
          0

theorem oeis_347865_conjecture_0 (n : ℕ) : (a n > 0) ↔ (n ≠ 744) := by
  sorry

theorem oeis_347865_conjecture_0.disproof : ¬ (type_of% @oeis_347865_conjecture_0) := by
  sorry
