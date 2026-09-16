import FormalConjectures.Util.ProblemImports

open Nat

noncomputable def A238224 (n : ℕ) : ℕ :=
  Finset.sum (Finset.Ico 1 n) fun j =>
    let upper_q : ℕ := (n - 1) / j
    Finset.sum (Finset.Icc 1 upper_q) fun q =>
      let k := j * q + 1
      if Nat.primeCounting (j * n) ∣ Nat.primeCounting (k * n) then 1 else 0

theorem oeis_238224_conjecture_0 : ∀ n : ℕ, 1 < n → A238224 n > 0 := by
  sorry

theorem oeis_238224_conjecture_0.disproof : ¬ (type_of% @oeis_238224_conjecture_0) := sorry
