import FormalConjectures.Util.ProblemImports
open Polynomial Finset Real Asymptotics Filter

noncomputable def P_q_factorial_poly (n : ℕ) : Polynomial ℕ :=
 (Icc 1 n).prod fun j =>
  (Finset.range j).sum fun i => C (1 : ℕ) * (X : Polynomial ℕ) ^ i

noncomputable def a (n : ℕ) : ℕ :=
  let P := P_q_factorial_poly n
  let max_degree : ℕ := n * (n - 1) / 2
  Finset.sum (Finset.range (max_degree + 1)) fun k => (P.coeff k) ^ 4

noncomputable def A_k_n (k n : ℕ) : ℝ :=
  let P := P_q_factorial_poly n
  let max_degree : ℕ := n * (n - 1) / 2
  (Finset.range (max_degree + 1)).sum fun j : ℕ => ((P.coeff j : ℝ) ^ k)

noncomputable def q_factorial_asymptotic_term_func (k n : ℕ) : ℝ :=
  let k_r : ℝ := k
  let n_r : ℝ := n
  let k_minus_one_half := (k_r - 1) / 2
  let c_k : ℝ := ((2 : ℝ) ^ k_minus_one_half * (3 : ℝ) ^ (k_r - 1)) / (sqrt k_r * Real.pi ^ k_minus_one_half)
  c_k * ((n.factorial : ℝ) ^ k_r / (n_r ^ (3 * k_minus_one_half)))

theorem oeis_380275_conjecture_general (k : ℕ) (hk : k > 0) :
  Asymptotics.IsEquivalent Filter.atTop (fun n => A_k_n k n) (q_factorial_asymptotic_term_func k) := by
  sorry

theorem oeis_380275_conjecture_general.disproof : ¬ (type_of% @oeis_380275_conjecture_general) := by
  sorry
