import FormalConjectures.Util.ProblemImports

open Nat

def A291624 (n : ℕ) : ℕ :=
  let B : ℕ := sqrt n
  Finset.sum (Finset.range (B + 1)) fun x =>
  Finset.sum (Finset.range (B + 1)) fun y =>
  Finset.sum (Finset.range (B + 1)) fun z =>
    let sq_sum_xyz := x^2 + y^2 + z^2
    if sq_sum_xyz ≤ n then
      let r := n - sq_sum_xyz
      let w := sqrt r
      if w^2 = r then
        let p := x + 2 * y + 5 * z
        if Nat.Prime p ∧ Nat.Prime (p - 2) ∧ Nat.Prime (p + 4)
        then 1
        else 0
      else 0
    else 0

theorem oeis_291624_conjecture_1 (n : ℕ) : n > 1 ∧ ¬ (4 ∣ n) → A291624 n > 0 := by
  sorry

theorem oeis_291624_conjecture_1.disproof : ¬ (type_of% @oeis_291624_conjecture_1) := by
  sorry
