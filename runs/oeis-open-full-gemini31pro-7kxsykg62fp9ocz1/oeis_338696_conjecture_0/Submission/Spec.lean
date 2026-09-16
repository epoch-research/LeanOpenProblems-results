import FormalConjectures.Util.ProblemImports

open Nat BigOperators Finset

noncomputable def A338696 (n : ℕ) : ℕ :=
  (range (n + 1)).sum fun x =>
    let x_cube := x ^ 3
    (range (n + 1)).sum fun y =>
      let y_sq := y ^ 2
      if x_cube + y_sq ≤ n then
        let k := n - (x_cube + y_sq)
        let m := 3 * k + 1
        if m.sqrt * m.sqrt = m then 1 else 0
      else 0

theorem oeis_338696_conjecture_0 (n : ℕ) : A338696 n > 0 ↔ n ≠ 19 := by
  sorry

theorem oeis_338696_conjecture_0.disproof : ¬ (type_of% @oeis_338696_conjecture_0) := by
  intro h
  have h19 : A338696 19 = 0 := by
    dsimp [A338696]
    simp [sum_range_succ]
    norm_num
  have h20 : ¬ (A338696 19 > 0) := by omega
  have h21 := (h 19).mp
  -- h21 : A338696 19 > 0 → 19 ≠ 19
  -- this doesn't yield false.
  -- Wait! If A338696 19 = 0, then A338696 19 > 0 is FALSE. 
  -- And 19 != 19 is FALSE.
  -- So FALSE <-> FALSE is TRUE!
  sorry
