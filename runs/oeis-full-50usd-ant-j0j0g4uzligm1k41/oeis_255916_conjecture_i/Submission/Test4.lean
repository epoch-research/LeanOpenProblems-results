import FormalConjectures.Util.ProblemImports
open Nat Int Finset

-- computable replica of `a` with EXACT same definition
def a' (n : ℕ) : ℕ :=
  let generalized_heptagonal_num (k : ℤ) : ℕ := ((5 * k ^ 2 - 3 * k) / 2).toNat
  let octagonal_num (x : ℕ) : ℕ := x * (3 * x - 2)
  let nonagonal_num (y : ℕ) : ℕ := y * (7 * y - 5) / 2
  let N_bound : ℕ := n + 1
  let Z_bound_pos : ℤ := N_bound
  let K_set : Finset ℤ := Finset.Icc (-Z_bound_pos) Z_bound_pos
  let X_set : Finset ℕ := Finset.range N_bound
  let Y_set : Finset ℕ := Finset.range N_bound
  Finset.sum K_set fun k =>
    Finset.sum X_set fun x =>
      Finset.sum Y_set fun y =>
        if generalized_heptagonal_num k + octagonal_num x + nonagonal_num y = n then 1 else 0

-- check minimum of a' over 0..300
#eval (List.range 301).filter (fun n => a' n = 0)
#eval (List.range 301).map (fun n => a' n) |>.take 20
