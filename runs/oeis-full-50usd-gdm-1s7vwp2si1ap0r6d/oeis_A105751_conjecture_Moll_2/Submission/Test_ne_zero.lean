import FormalConjectures.Util.ProblemImports

open Complex Filter Asymptotics Topology

noncomputable def a (n : ℕ) : ℤ :=
  let product_term (k : ℕ) : ℂ := 1 + (k : ℂ) * I
  Int.floor (((Finset.range (n + 1)).prod product_term).im)

open Nat

def P : ℕ → ℤ × ℤ
  | 0 => (1, 0)
  | n + 1 =>
    let (x, y) := P n
    (x - (n + 1) * y, (n + 1) * x + y)

theorem a_eq_P_im (n : ℕ) : a n = (P n).2 := sorry

lemma a_ne_zero (n : ℕ) (hn : n ≥ 4) : a n ≠ 0 := by
  sorry
