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
#check Nat.sum_four_squares
#check Nat.eq_sq_add_sq_iff
#check Nat.eq_sq_add_sq_iff_eq_sq_mul
#check Nat.Prime.sq_add_sq
#check IsPrimitiveRoot
#check Zsqrtd
#check GaussianInt
