import FormalConjectures.Util.ProblemImports

open Polynomial Finset Real Asymptotics Filter

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


lemma geom_factor_natDegree_le (j : ℕ) :
    (((Finset.range j).sum fun i => C (1 : ℕ) * (X : Polynomial ℕ) ^ i).natDegree ≤ j - 1) := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro N hN
  rw [Polynomial.finset_sum_coeff]
  apply Finset.sum_eq_zero
  intro i hi
  simp only [Polynomial.coeff_C_mul_X_pow]
  rw [if_neg]
  intro hEq
  subst hEq
  exact not_lt_of_ge (Nat.le_sub_one_of_lt (by simpa using hi)) hN

lemma sum_Icc_pred (n : ℕ) : ∑ j ∈ Finset.Icc 1 n, (j - 1) = n * (n - 1) / 2 := by
  rw [← Finset.Ico_add_one_right_eq_Icc (1 : ℕ) n]
  rw [Finset.sum_Ico_eq_sum_range]
  simp
  exact Finset.sum_range_id n

lemma P_q_factorial_poly_natDegree_le (n : ℕ) :
    (P_q_factorial_poly n).natDegree ≤ n * (n - 1) / 2 := by
  unfold P_q_factorial_poly
  calc
    (∏ j ∈ Finset.Icc 1 n, (Finset.range j).sum fun i => C (1 : ℕ) * (X : Polynomial ℕ) ^ i).natDegree
        ≤ ∑ j ∈ Finset.Icc 1 n, ((Finset.range j).sum fun i => C (1 : ℕ) * (X : Polynomial ℕ) ^ i).natDegree :=
      Polynomial.natDegree_prod_le _ _
    _ ≤ ∑ j ∈ Finset.Icc 1 n, (j - 1) := by
      exact Finset.sum_le_sum fun j hj => geom_factor_natDegree_le j
    _ = n * (n - 1) / 2 := sum_Icc_pred n

lemma eval_one_factor (j : ℕ) :
    Polynomial.eval (1 : ℕ) ((Finset.range j).sum fun i => C (1 : ℕ) * (X : Polynomial ℕ) ^ i) = j := by
  rw [Polynomial.eval_finset_sum]
  simp

lemma P_q_factorial_poly_eval_one (n : ℕ) : (P_q_factorial_poly n).eval 1 = n.factorial := by
  unfold P_q_factorial_poly
  rw [Polynomial.eval_prod]
  simp
  rw [← Finset.Ico_add_one_right_eq_Icc (1 : ℕ) n]
  exact Finset.prod_Ico_id_eq_factorial n

lemma A_k_n_one_eq_factorial (n : ℕ) : A_k_n 1 n = (n.factorial : ℝ) := by
  unfold A_k_n
  let P := P_q_factorial_poly n
  let m : ℕ := n * (n - 1) / 2
  have hdeg : P.natDegree < m + 1 := Nat.lt_succ_of_le (by simpa [P, m] using P_q_factorial_poly_natDegree_le n)
  have heval := Polynomial.eval_eq_sum_range' (p := P) hdeg (1 : ℕ)
  have hsum_nat : ∑ j ∈ Finset.range (m + 1), P.coeff j = n.factorial := by
    have heval' : P.eval 1 = ∑ j ∈ Finset.range (m + 1), P.coeff j := by
      simpa using heval
    rw [← heval', show P.eval 1 = n.factorial by simpa [P] using P_q_factorial_poly_eval_one n]
  have hcast : ((∑ j ∈ Finset.range (m + 1), P.coeff j : ℕ) : ℝ) = (n.factorial : ℝ) := by
    exact_mod_cast hsum_nat
  rw [← hcast]
  simp only [P, m]
  rw [Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro j hj
  norm_num

lemma q_factorial_asymptotic_term_func_one (n : ℕ) :
    q_factorial_asymptotic_term_func 1 n = (n.factorial : ℝ) := by
  unfold q_factorial_asymptotic_term_func
  norm_num

lemma oeis_380275_conjecture_k_one :
  Asymptotics.IsEquivalent Filter.atTop (fun n => A_k_n 1 n) (q_factorial_asymptotic_term_func 1) := by
  apply EventuallyEq.isEquivalent
  filter_upwards [] with n
  simp [A_k_n_one_eq_factorial, q_factorial_asymptotic_term_func_one]

/-- oeis_380275_conjecture_general:
Conjecture: In general, sum of the k-th powers of the coefficients of q in the q-factorials
is asymptotic to
$$ 2^{\frac{k-1}{2}} \cdot 3^{k-1} \cdot n!^k / (\sqrt{k} \cdot \pi^{\frac{k-1}{2}} \cdot n^{\frac{3(k-1)}{2}}) $$
We require $k > 0$ for the formula to be well-defined (due to $\sqrt{k}$).
-/
theorem oeis_380275_conjecture_general (k : ℕ) (hk : k > 0) :
  Asymptotics.IsEquivalent Filter.atTop (fun n => A_k_n k n) (q_factorial_asymptotic_term_func k) :=
by sorry
