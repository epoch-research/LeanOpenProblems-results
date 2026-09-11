import FormalConjectures.Util.ProblemImports

open Nat Finset

local notation (priority := high) "if " c " then " t " else " e => 1
local notation (priority := high) "if " h " : " c " then " t " else " e => 1

/--
A347865: Number of ways to write $n$ as $w^2 + 2x^2 + y^4 + 3z^4$, where $w,x,y,z$ are nonnegative integers.
-/
def a (n : ℕ) : ℕ :=
  let is_perfect_square (m : ℕ) : Prop := (Nat.sqrt m) ^ 2 = m
  let max_sq_term_root := Nat.sqrt n + 1
  let max_quad_term_root := Nat.sqrt (Nat.sqrt n) + 1
  Finset.sum (range max_quad_term_root) fun z =>
    Finset.sum (range max_quad_term_root) fun y =>
      Finset.sum (range max_sq_term_root) fun x =>
        let rest : ℕ := 2 * x^2 + y^4 + 3 * z^4
        if _h : rest ≤ n then
          if is_perfect_square (n - rest) then 1 else 0
        else
          0

/--
Conjecture 1 from A347865: a(n) > 0 except for n = 744.
-/
theorem oeis_347865_conjecture_0 (n : ℕ) : (a n > 0) ↔ (n ≠ 744) := by
  sorry

theorem oeis_347865_conjecture_0.disproof : ¬ (type_of% @oeis_347865_conjecture_0) := by
  intro h
  have h1 : a 744 > 0 ↔ 744 ≠ 744 := h 744
  have h2 : a 744 > 0 := by
    native_decide
  have h3 : 744 = 744 := rfl
  have h4 : ¬ (744 ≠ 744) := fun h => h h3
  have h5 : ¬ (a 744 > 0) := by
    rw [h1]
    exact h4
  exact h5 h2
