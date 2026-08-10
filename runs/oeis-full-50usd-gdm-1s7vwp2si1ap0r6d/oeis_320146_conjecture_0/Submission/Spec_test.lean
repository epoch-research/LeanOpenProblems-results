import FormalConjectures.Util.ProblemImports

open Nat

noncomputable def A320146 (n : ℕ) : ℕ :=
  let P i : ℕ := Nat.nth Nat.Prime i
  (2 * P (n - 1)) % (P (n - 2) + P n)

noncomputable def prime_oeis (n : ℕ) : ℕ :=
  Nat.nth Nat.Prime (n - 1)

theorem oeis_320146_conjecture_0 :
  ∃ L : ℝ, Filter.Tendsto
    (fun n : ℕ =>
      (Finset.sum (Finset.Icc 2 n) (fun i => (A320146 i : ℝ)))
      /
      (Finset.sum (Finset.Icc 2 n) (fun i => (prime_oeis i : ℝ))))
    Filter.atTop
    (nhds L) :=
  answer(sorry)
