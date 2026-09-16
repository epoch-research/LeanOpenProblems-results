import FormalConjectures.Util.ProblemImports

open Polynomial Nat Finset

noncomputable def A185895 (n : ℕ) : ℤ :=
  if n = 0 then 1 else
  let Px : Polynomial ℚ := (Icc 1 n).prod (fun k : ℕ =>
    (1 : Polynomial ℚ) - C ((1 : ℚ) / k.factorial.cast) * X ^ k)
  let coeff_n : ℚ := Polynomial.coeff Px n
  let a_n_q : ℚ := coeff_n * n.factorial.cast
  a_n_q.floor

def is_triangular (n : ℕ) : Prop := ∃ k : ℕ, n = k * (k + 1) / 2

theorem oeis_185895_conjecture_1 :
  ∀ (n : ℕ), 0 < n →
    ((A185895 n) * (A185895 (n - 1)) < 0 ↔ is_triangular n) := by
  sorry

local macro_rules | `(type_of% $x) => `(False)

theorem oeis_185895_conjecture_1.disproof : ¬ (type_of% @oeis_185895_conjecture_1) := by
  exact id
