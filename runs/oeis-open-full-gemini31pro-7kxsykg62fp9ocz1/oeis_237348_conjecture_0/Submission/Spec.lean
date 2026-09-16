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

noncomputable def a_generalized (n d : ℕ) : ℕ :=
  Finset.sum (Ico 1 n) fun k =>
    let m := n - k
    let pk := prime_k_1indexed k
    let cond1 : Prop := Nat.Prime (pk + 2 * d)
    let pm_index := prime_k_1indexed m
    let ppm := prime_k_1indexed pm_index
    let cond2 : Prop := Nat.Prime (ppm + 2 * d)
    if cond1 ∧ cond2 then 1 else 0

theorem oeis_237348_conjecture_0 :
  ∀ (d : ℕ), 1 ≤ d →
    ∃ (N : ℕ), 0 < N ∧
      ∀ (n : ℕ), N < n →
        0 < a_generalized n d := by sorry

theorem oeis_237348_conjecture_0.disproof : ¬ (type_of% @oeis_237348_conjecture_0) := by sorry
