import FormalConjectures.Util.ProblemImports
open Nat Finset
noncomputable def prime_k_1indexed (k : ℕ) : ℕ := Nat.nth Nat.Prime (k - 1)
noncomputable def a (n : ℕ) : ℕ :=
  Finset.sum (Ico 1 n) fun k =>
    let m := n - k
    let pk := prime_k_1indexed k
    let cond1 : Prop := Nat.Prime (pk + 4)
    let pm_index := prime_k_1indexed m
    let ppm := prime_k_1indexed pm_index
    let cond2 : Prop := Nat.Prime (ppm + 4)
    if cond1 ∧ cond2 then 1 else 0
example : prime_k_1indexed 1 = 2 := by
  unfold prime_k_1indexed
  norm_num [Nat.nth_count (p := Nat.Prime) (by norm_num : Nat.Prime 2)]
