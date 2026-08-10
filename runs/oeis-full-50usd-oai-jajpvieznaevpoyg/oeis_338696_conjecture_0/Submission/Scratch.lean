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

example : A338696 19 = 0 := by
  norm_num [A338696]

example : A338696 20 > 0 := by
  norm_num [A338696]

example (n : ℕ) (h : A338696 n > 0) : n ≠ 19 := by
  intro hn
  subst hn
  norm_num [A338696] at h
