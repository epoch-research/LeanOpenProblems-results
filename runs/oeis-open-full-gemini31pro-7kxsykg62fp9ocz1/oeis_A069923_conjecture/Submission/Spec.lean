import FormalConjectures.Util.ProblemImports

open Nat

noncomputable def a (n : ℕ) : ℕ :=
  if n = 0 then 0
  else
    let p_n : ℕ := Nat.nth Nat.Prime (n - 1)
    let L := 2^n
    let U := L + p_n
    primeCounting U - primeCounting (L - 1)

theorem oeis_A069923_conjecture (n : ℕ) (hn : 0 < n) :
  1 ≤ a n :=
by sorry

theorem oeis_A069923_conjecture.disproof : ¬ (type_of% @oeis_A069923_conjecture) := by
  intro h
  have H := h 1 (by decide)
  revert H
  unfold a
  norm_num
  sorry
