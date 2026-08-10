import FormalConjectures.Util.ProblemImports

open Finset Nat

noncomputable def a (n : ℕ) : ℚ :=
  match n with
  | 0 => 1
  | m_plus_one@(m + 1) =>
    let sum_val : ℚ := Finset.sum (Finset.range m_plus_one) (fun k =>
      let j : ℕ := k + 1
      let a_term : ℚ := a (m_plus_one - j)
      let coeff_factor : ℚ := 1 - (-1 : ℚ)^j - (-2 : ℚ)^j
      (m_plus_one.choose j : ℚ) * coeff_factor * a_term
    )
    (-1 : ℚ)^m_plus_one + (1 / 2) * sum_val

def C (j : ℕ) : ℤ :=
  if j % 2 = 0 then - (2 ^ (j - 1)) else 1 + 2 ^ (j - 1)

lemma C_spec (j : ℕ) (hj : 1 ≤ j) :
    2 * C j = 1 - (-1 : ℤ)^j - (-2 : ℤ)^j := by
  sorry

noncomputable def a_int (n : ℕ) : ℤ :=
  match n with
  | 0 => 1
  | m + 1 =>
    let sum_val : ℤ := Finset.sum (Finset.range (m + 1)) (fun k =>
      let j := k + 1
      ((m + 1).choose j : ℤ) * C j * a_int (m + 1 - j)
    )
    (-1 : ℤ)^(m + 1) + sum_val

theorem a_eq_a_int (n : ℕ) : a n = (a_int n : ℚ) := by
  sorry
