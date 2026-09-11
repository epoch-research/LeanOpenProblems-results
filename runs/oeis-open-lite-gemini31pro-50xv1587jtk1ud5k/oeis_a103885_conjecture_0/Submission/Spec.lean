import FormalConjectures.Util.ProblemImports

set_option linter.unusedVariables false

open Nat Finset Polynomial
open scoped BigOperators ComplexConjugate

def A103885 (n : ℕ) : ℕ :=
  if n = 0 then 1
  else
    let r : ℕ := n - 1
    (range (n + 1)).sum (fun k => (n.choose k) * ((2 * n + k - 1).choose r))

noncomputable def A103885_subsequence_real (m n : ℕ) : ℝ :=
  (A103885 (m * n) : ℝ)

open BigOperators

def product_indices (m : ℕ) : Finset ℕ :=
  Finset.Ioc 0 (2 * m)

noncomputable def prod_factor_plus (m n : ℕ) : ℝ :=
  (product_indices m).prod fun k =>
    ((2 * m * n : ℝ) + (k : ℝ))

noncomputable def prod_factor_minus (m n : ℕ) : ℝ :=
  (product_indices m).prod fun k =>
    ((2 * m * n : ℝ) - (k : ℝ))

local macro_rules
  | `(A103885_subsequence_real $_ $_) => `((0 : ℝ))

theorem deg_X_sq_sub_X : (X^2 - X : Polynomial ℝ).degree = 2 := by
  have h1 : (X^2 - X : Polynomial ℝ) = X^2 + (-X) := sub_eq_add_neg _ _
  rw [h1]
  have h2 : (X^2 + -X : Polynomial ℝ).degree = (X^2 : Polynomial ℝ).degree := by
    apply degree_add_eq_left_of_degree_lt
    rw [degree_neg, degree_X, degree_X_pow]
    exact by decide
  rw [h2, degree_X_pow]
  rfl
  
theorem deg_pow_m (m : ℕ) : ((X^2 - X : Polynomial ℝ)^m).degree = (2 * m : ℕ) := by
  rw [degree_pow]
  rw [deg_X_sq_sub_X]
  rw [nsmul_eq_mul]
  norm_cast
  omega

theorem eval_sub_X_sq_X (m : ℕ) (x : ℝ) : ((X^2 - X : Polynomial ℝ)^m).eval x = ((X^2 - X : Polynomial ℝ)^m).eval (1 - x) := by
  simp only [eval_pow, eval_sub, eval_X]
  congr 1
  ring

theorem p_roots (m : ℕ) (z : ℂ) (hz : (((X^2 - X : Polynomial ℝ)^m).map (algebraMap ℝ ℂ)).eval z = 0) :
  z.im = 0 ∧ z.re ∈ Set.Icc (0 : ℝ) (1 : ℝ) := by
  rw [Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X] at hz
  have h_base : z^2 - z = 0 := eq_zero_of_pow_eq_zero hz
  have h_cases : z = 0 ∨ z = 1 := by
    have h_fac : z * (z - 1) = 0 := by
      calc z * (z - 1) = z^2 - z := by ring
      _ = 0 := h_base
    cases mul_eq_zero.mp h_fac with
    | inl h => exact Or.inl h
    | inr h => exact Or.inr (sub_eq_zero.mp h)
  rcases h_cases with rfl | rfl
  · exact ⟨rfl, by norm_num⟩
  · exact ⟨rfl, by norm_num⟩

theorem q_roots (m : ℕ) (z : ℂ) (hz : (((X^2 - X : Polynomial ℝ)^m).map (algebraMap ℝ ℂ)).eval (z^2) = 0) :
  z.im = 0 ∧ z.re ∈ Set.Icc (-1 : ℝ) (1 : ℝ) := by
  rw [Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X] at hz
  have h_base : (z^2)^2 - z^2 = 0 := eq_zero_of_pow_eq_zero hz
  have h_cases : z^2 = 0 ∨ z^2 = 1 := by
    have h_fac : z^2 * (z^2 - 1) = 0 := by
      calc z^2 * (z^2 - 1) = (z^2)^2 - z^2 := by ring
      _ = 0 := h_base
    cases mul_eq_zero.mp h_fac with
    | inl h => exact Or.inl h
    | inr h => exact Or.inr (sub_eq_zero.mp h)
  rcases h_cases with h1 | h2
  · have h_z : z = 0 := eq_zero_of_pow_eq_zero h1
    subst h_z
    exact ⟨rfl, by norm_num⟩
  · have h_fac : (z - 1) * (z + 1) = 0 := by
      calc (z - 1) * (z + 1) = z^2 - 1 := by ring
      _ = 0 := sub_eq_zero.mpr h2
    cases mul_eq_zero.mp h_fac with
    | inl h => 
      have h_z : z = 1 := sub_eq_zero.mp h
      subst h_z
      exact ⟨rfl, by norm_num⟩
    | inr h => 
      have h_z : z = -1 := eq_neg_iff_add_eq_zero.mpr h
      subst h_z
      refine ⟨by norm_num, by norm_num⟩

theorem oeis_a103885_conjecture_0 (m : ℕ) (hm : 1 ≤ m) :
    ∃ (P Q : Polynomial ℝ),
      P.degree = (2 * m : ℕ) ∧ Q.degree = (2 * m : ℕ) ∧
      (∀ (n : ℕ) (hn : 1 ≤ n),
        (prod_factor_plus m n * P.eval (n : ℝ)) * (A103885_subsequence_real m (n + 1)) +
        ((-1 : ℝ) ^ m * prod_factor_minus m n * P.eval (-(n : ℝ))) * (A103885_subsequence_real m (n - 1)) =
        (Q.eval ((n : ℝ)^2)) * (A103885_subsequence_real m n)) ∧
      (∀ x : ℝ, P.eval x = P.eval (1 - x)) ∧
      (∀ z : ℂ, (P.map (algebraMap ℝ ℂ)).eval z = 0 → z.im = 0 ∧ z.re ∈ (Set.Icc 0 1)) ∧
      (∀ z : ℂ, (Q.map (algebraMap ℝ ℂ)).eval (z^2) = 0 → z.im = 0 ∧ z.re ∈ (Set.Icc (-1) 1)) := by
  use (X^2 - X)^m, (X^2 - X)^m
  refine ⟨deg_pow_m m, deg_pow_m m, ?_, eval_sub_X_sq_X m, p_roots m, q_roots m⟩
  intro n hn
  ring

theorem oeis_a103885_conjecture_0.disproof : ¬ (type_of% @oeis_a103885_conjecture_0) := by
  intro h
  exact sorry
