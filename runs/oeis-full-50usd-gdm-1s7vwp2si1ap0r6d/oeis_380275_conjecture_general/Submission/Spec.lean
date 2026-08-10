/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import FormalConjectures.Util.ProblemImports

open Polynomial Finset Real Asymptotics Filter

set_option linter.unusedVariables false
set_option linter.style.copyright.formalConjectures false
set_option linter.style.namespace false

-- [START USER PROVIDED CODE]
/--
A380275: Sum of the fourth powers of the coefficients of $q$ in the $q$-factorials.
The $q$-factorial polynomial $P_n(q)$ is given by
$$P_n(q) = \prod_{j=1}^n \frac{1-q^j}{1-q} = \prod_{j=1}^n \sum_{i=0}^{j-1} q^i$$
The sequence is defined by
$$a(n) : \sum_{k \ge 0} \left([q^k] P_n(q)\right)^4$$
-/
noncomputable def P_q_factorial_poly (n : ℕ) : Polynomial ℕ :=
 (Icc 1 n).prod fun j =>
  -- $\sum_{i=0}^{j-1} X^i$
  (Finset.range j).sum fun i => C (1 : ℕ) * (X : Polynomial ℕ) ^ i

noncomputable def a (n : ℕ) : ℕ :=
  let P := P_q_factorial_poly n
  -- The maximum degree of $P_n$ is $n(n-1)/2$.
  let max_degree : ℕ := n * (n - 1) / 2

  Finset.sum (Finset.range (max_degree + 1)) fun k => (P.coeff k) ^ 4

/-- Generalized sequence: Sum of $k$-th powers of coefficients of $q$-factorial.
We cast to $\mathbb{R}$ for asymptotic analysis. -/
noncomputable def A_k_n (k n : ℕ) : ℝ :=
  let P := P_q_factorial_poly n
  let max_degree : ℕ := n * (n - 1) / 2
  (Finset.range (max_degree + 1)).sum fun j : ℕ => ((P.coeff j : ℝ) ^ k)

/-- The conjectured asymptotic formula for the sum of $k$-th powers of coefficients of the $q$-factorial.
Note: this function is only relevant for $k>0$ and large $n$. -/
noncomputable def q_factorial_asymptotic_term_func (k n : ℕ) : ℝ :=
  let k_r : ℝ := k
  let n_r : ℝ := n
  let k_minus_one_half := (k_r - 1) / 2
  -- Define Constant C_k
  let c_k : ℝ := ((2 : ℝ) ^ k_minus_one_half * (3 : ℝ) ^ (k_r - 1)) / (sqrt k_r * Real.pi ^ k_minus_one_half)

  -- Define the N-dependent term
  c_k * ((n.factorial : ℝ) ^ k_r / (n_r ^ (3 * k_minus_one_half)))

theorem q_factorial_asymptotic_term_func_one (n : ℕ) :
  q_factorial_asymptotic_term_func 1 n = (n.factorial : ℝ) := by
  unfold q_factorial_asymptotic_term_func
  simp

theorem eval_P_q_factorial_poly (n : ℕ) : (P_q_factorial_poly n).eval 1 = n.factorial := by
  unfold P_q_factorial_poly
  simp [eval_prod]
  rw [← Ico_add_one_right_eq_Icc 1, prod_Ico_id_eq_factorial]

theorem factor_natDegree_le (j : ℕ) : ((Finset.range j).sum fun i => C (1 : ℕ) * (X : Polynomial ℕ) ^ i).natDegree ≤ j - 1 := by
  rcases j with _ | j
  · simp
  · simp only [Nat.succ_sub_succ_eq_sub, Nat.sub_zero]
    refine natDegree_sum_le_of_forall_le (Finset.range (j + 1)) (fun i => C (1 : ℕ) * (X : Polynomial ℕ) ^ i) (fun i hi => ?_)
    simp only [Finset.mem_range] at hi
    have h_deg : (C (1 : ℕ) * (X : Polynomial ℕ) ^ i).natDegree ≤ i := by
      refine le_trans (natDegree_mul_le) ?_
      simp
    exact le_trans h_deg (by omega)

theorem sum_Icc_sub_one_nat (n : ℕ) : 2 * ∑ i ∈ Icc 1 n, (i - 1) = n * (n - 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h_insert : Icc 1 (n + 1) = insert (n + 1) (Icc 1 n) := by
      ext x
      simp only [mem_Icc, mem_insert]
      omega
    rw [h_insert]
    have h_notmem : n + 1 ∉ Icc 1 n := by
      simp only [mem_Icc]
      omega
    rw [sum_insert h_notmem]
    simp only [Nat.add_succ_sub_one, add_zero]
    rw [left_distrib]
    rw [ih]
    rcases n with _ | n
    · simp
    · simp only [Nat.succ_sub_succ_eq_sub, Nat.sub_zero]
      ring

theorem P_q_factorial_poly_natDegree_le (n : ℕ) : (P_q_factorial_poly n).natDegree ≤ n * (n - 1) / 2 := by
  unfold P_q_factorial_poly
  have h_prod := natDegree_prod_le (Icc 1 n) (fun j => (range j).sum (fun i => C (1 : ℕ) * (X : Polynomial ℕ) ^ i))
  refine le_trans h_prod ?_
  have h_le : ∑ i ∈ Icc 1 n, ((range i).sum (fun i => C (1 : ℕ) * (X : Polynomial ℕ) ^ i)).natDegree ≤
              ∑ i ∈ Icc 1 n, (i - 1) := by
    refine sum_le_sum (fun i hi => ?_)
    exact factor_natDegree_le i
  have h_sum := sum_Icc_sub_one_nat n
  have h_div : ∑ i ∈ Icc 1 n, (i - 1) = n * (n - 1) / 2 := by
    omega
  omega

theorem A_k_n_one (n : ℕ) :
  A_k_n 1 n = (n.factorial : ℝ) := by
  unfold A_k_n
  simp only [pow_one]
  have h_sum : ∑ j ∈ range (n * (n - 1) / 2 + 1), ((P_q_factorial_poly n).coeff j : ℝ) =
               ((∑ j ∈ range (n * (n - 1) / 2 + 1), (P_q_factorial_poly n).coeff j : ℕ) : ℝ) := by
    simp
  rw [h_sum]
  have h_eval : (P_q_factorial_poly n).eval 1 = ∑ j ∈ range (n * (n - 1) / 2 + 1), (P_q_factorial_poly n).coeff j := by
    have h_le := P_q_factorial_poly_natDegree_le n
    have h_lt : (P_q_factorial_poly n).natDegree < n * (n - 1) / 2 + 1 := by
      omega
    have h_sum' := eval_eq_sum_range' h_lt (1 : ℕ)
    simp at h_sum'
    exact h_sum'
  rw [← h_eval]
  rw [eval_P_q_factorial_poly n]

theorem oeis_380275_conjecture_k_1 :
  Asymptotics.IsEquivalent Filter.atTop (fun n => A_k_n 1 n) (q_factorial_asymptotic_term_func 1) := by
  have h1 : (fun n => A_k_n 1 n) = (fun n => (n.factorial : ℝ)) := by
    ext n
    exact A_k_n_one n
  have h2 : q_factorial_asymptotic_term_func 1 = (fun n => (n.factorial : ℝ)) := by
    ext n
    exact q_factorial_asymptotic_term_func_one n
  rw [h1, h2]

/-- oeis_380275_conjecture_general:
Conjecture: In general, sum of the k-th powers of the coefficients of q in the q-factorials
is asymptotic to
$$ 2^{\frac{k-1}{2}} \cdot 3^{k-1} \cdot n!^k / (\sqrt{k} \cdot \pi^{\frac{k-1}{2}} \cdot n^{\frac{3(k-1)}{2}}) $$
We require $k > 0$ for the formula to be well-defined (due to $\sqrt{k}$).
-/
theorem oeis_380275_conjecture_general (k : ℕ) (hk : k > 0) :
  Asymptotics.IsEquivalent Filter.atTop (fun n => A_k_n k n) (q_factorial_asymptotic_term_func k) := by
  rcases eq_or_ne k 1 with rfl | hk1
  · exact oeis_380275_conjecture_k_1
  · sorry

