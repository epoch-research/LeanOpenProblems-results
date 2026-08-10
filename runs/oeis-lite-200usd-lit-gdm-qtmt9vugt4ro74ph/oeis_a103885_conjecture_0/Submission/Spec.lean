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

open Nat Finset Polynomial
open scoped BigOperators ComplexConjugate
set_option warn.sorry false
set_option google.answer "always_true"
set_option linter.style.copyright.formalConjectures false
set_option linter.style.namespace false
set_option linter.unusedVariables false


/--
A103885: $a(n) = [x^{2n}] \left(\frac{1 + x}{1 - x}\right)^n$.
The sequence is given by the combinatorial identity:
$$a(n) = \sum_{k = 0}^n \binom{n}{k} \binom{2n+k-1}{n-1}$$
with $a(0) = 1$.
-/
def A103885 (n : ℕ) : ℕ :=
  if n = 0 then 1
  else
    let r : ℕ := n - 1
    (range (n + 1)).sum (fun k => (n.choose k) * ((2 * n + k - 1).choose r))

-- The sequence b(n) = a(m*n) lifted to ℝ (Original definition untouched)
noncomputable def A103885_subsequence_real (m n : ℕ) : ℝ :=
  (A103885 (m * n) : ℝ)

open BigOperators

-- The indices k = 1 to 2m, used in the product
private def product_indices (m : ℕ) : Finset ℕ :=
  Finset.Ioc 0 (2 * m)

-- The factor Product_{k=1}^{2m} (2mn + k)
noncomputable def prod_factor_plus (m n : ℕ) : ℝ :=
  (product_indices m).prod fun k =>
    ((2 * m * n : ℝ) + (k : ℝ))

-- The factor Product_{k=1}^{2m} (2mn - k)
noncomputable def prod_factor_minus (m n : ℕ) : ℝ :=
  (product_indices m).prod fun k =>
    ((2 * m * n : ℝ) - (k : ℝ))


noncomputable def P_1 : Polynomial ℝ := 5 * X^2 - 5 * X + 1

theorem P_1_roots (z : ℂ) (hz : (P_1.map (algebraMap ℝ ℂ)).eval z = 0) :
    z.im = 0 ∧ z.re ∈ (Set.Icc 0 1) := by
  have h_map : (P_1.map (algebraMap ℝ ℂ)).eval z = 5 * z^2 - 5 * z + 1 := by
    unfold P_1
    simp [Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_one, Polynomial.map_ofNat]
  rw [hz] at h_map
  have h_sq : 5 * (z - 1/2)^2 - 1/4 = 5 * z^2 - 5 * z + 1 := by
    ring
  rw [← h_sq] at h_map
  have h_eq : 5 * (z - 1/2)^2 = 1/4 := by
    linear_combination -h_map
  have h_sq2 : (z - 1/2)^2 = 1/20 := by
    calc
      (z - 1/2)^2 = (5 * (z - 1/2)^2) / 5 := by ring
      _ = (1/4) / 5 := by rw [h_eq]
      _ = 1/20 := by ring
  -- Now we take real and imaginary parts of both sides
  have h_re : ((z - 1/2)^2).re = (1/20 : ℂ).re := by rw [h_sq2]
  have h_im : ((z - 1/2)^2).im = (1/20 : ℂ).im := by rw [h_sq2]
  simp at h_re h_im
  have h_sq3 : (z - 2⁻¹)^2 = (z - 2⁻¹) * (z - 2⁻¹) := by ring
  have h_re2 : ((z - 2⁻¹) * (z - 2⁻¹)).re = 20⁻¹ := by rw [← h_sq3, h_re]
  have h_im2 : ((z - 2⁻¹) * (z - 2⁻¹)).im = 0 := by rw [← h_sq3, h_im]
  simp [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im] at h_re2 h_im2
  have h_im_eq : 2 * (z.re - 2⁻¹) * z.im = 0 := by
    calc
      2 * (z.re - 2⁻¹) * z.im = (z.re - 2⁻¹) * z.im + z.im * (z.re - 2⁻¹) := by ring
      _ = 0 := h_im2
  have h_prod : (z.re - 2⁻¹) * z.im = 0 := by linarith
  have hz_im : z.im = 0 := by
    cases mul_eq_zero.mp h_prod with
    | inr h_im_zero => exact h_im_zero
    | inl h_re_zero =>
      have h_contr : z.im * z.im < 0 := by
        calc
          z.im * z.im = (z.re - 2⁻¹) * (z.re - 2⁻¹) - 20⁻¹ := by linarith
          _ = 0 * 0 - 20⁻¹ := by rw [h_re_zero]
          _ = - 20⁻¹ := by ring
          _ < 0 := by norm_num
      have h_nonneg := mul_self_nonneg z.im
      linarith
  have h_sq_re : (z.re - 2⁻¹) * (z.re - 2⁻¹) = 20⁻¹ := by
    calc
      (z.re - 2⁻¹) * (z.re - 2⁻¹) = (z.re - 2⁻¹) * (z.re - 2⁻¹) - z.im * z.im := by rw [hz_im]; ring
      _ = 20⁻¹ := h_re2
  have h_ge_zero : 0 ≤ z.re := by
    by_contra h_neg
    have h1 : z.re - 2⁻¹ < - 2⁻¹ := by linarith
    have h2 : (z.re - 2⁻¹) * (z.re - 2⁻¹) > 4⁻¹ := by nlinarith
    linarith [h_sq_re]
  have h_le_one : z.re ≤ 1 := by
    by_contra h_gt
    have h1 : z.re - 2⁻¹ > 2⁻¹ := by linarith
    have h2 : (z.re - 2⁻¹) * (z.re - 2⁻¹) > 4⁻¹ := by nlinarith
    linarith [h_sq_re]
  have h_mem : z.re ∈ Set.Icc (0 : ℝ) 1 := Set.mem_Icc.mpr ⟨h_ge_zero, h_le_one⟩
  exact ⟨hz_im, h_mem⟩

theorem P_1_sym (x : ℝ) : P_1.eval x = P_1.eval (1 - x) := by
  unfold P_1
  simp
  ring

theorem P_1_deg : P_1.degree = (2 : ℕ) := by
  unfold P_1
  compute_degree!

noncomputable def Q_1 : Polynomial ℝ := 220 * X^2 - 136 * X + 12

theorem Q_1_deg : Q_1.degree = (2 : ℕ) := by
  unfold Q_1
  compute_degree!

theorem Q_1_roots_w (w : ℂ) (hw : 220 * w^2 - 136 * w + 12 = 0) :
    w.im = 0 ∧ w.re ∈ (Set.Icc 0 1) := by
  have h_eq : 55 * (w - 17/55)^2 = 124/55 := by
    calc
      55 * (w - 17/55)^2 = (220 * w^2 - 136 * w + 12) / 4 + 124/55 := by ring
      _ = 0 / 4 + 124/55 := by rw [hw]
      _ = 124/55 := by ring
  have h_sq2 : (w - 17/55)^2 = 124/3025 := by
    calc
      (w - 17/55)^2 = (55 * (w - 17/55)^2) / 55 := by ring
      _ = (124/55) / 55 := by rw [h_eq]
      _ = 124/3025 := by ring
  -- Take real and imaginary parts
  have h_re : ((w - 17/55)^2).re = (124/3025 : ℂ).re := by rw [h_sq2]
  have h_im : ((w - 17/55)^2).im = (124/3025 : ℂ).im := by rw [h_sq2]
  simp at h_re h_im
  have h_sq3 : (w - 17/55)^2 = (w - 17/55) * (w - 17/55) := by ring
  have h_re2 : ((w - 17/55) * (w - 17/55)).re = 124/3025 := by rw [← h_sq3, h_re]
  have h_im2 : ((w - 17/55) * (w - 17/55)).im = 0 := by rw [← h_sq3, h_im]
  simp [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im] at h_re2 h_im2
  have h_im_eq : 2 * (w.re - 17/55) * w.im = 0 := by
    calc
      2 * (w.re - 17/55) * w.im = (w.re - 17/55) * w.im + w.im * (w.re - 17/55) := by ring
      _ = 0 := h_im2
  have h_prod : (w.re - 17/55) * w.im = 0 := by linarith
  have hw_im : w.im = 0 := by
    cases mul_eq_zero.mp h_prod with
    | inr h_im_zero => exact h_im_zero
    | inl h_re_zero =>
      have h_contr : w.im * w.im < 0 := by
        calc
          w.im * w.im = (w.re - 17/55) * (w.re - 17/55) - 124/3025 := by linarith
          _ = 0 * 0 - 124/3025 := by rw [h_re_zero]
          _ = - 124/3025 := by ring
          _ < 0 := by norm_num
      have h_nonneg := mul_self_nonneg w.im
      linarith
  have h_sq_re : (w.re - 17/55) * (w.re - 17/55) = 124/3025 := by
    calc
      (w.re - 17/55) * (w.re - 17/55) = (w.re - 17/55) * (w.re - 17/55) - w.im * w.im := by rw [hw_im]; ring
      _ = 124/3025 := h_re2
  have h_ge_zero : 0 ≤ w.re := by
    by_contra h_neg
    have h1 : w.re - 17/55 < - 17/55 := by linarith
    have h2 : (w.re - 17/55) * (w.re - 17/55) > 289/3025 := by nlinarith
    linarith [h_sq_re]
  have h_le_one : w.re ≤ 1 := by
    by_contra h_gt
    have h1 : w.re - 17/55 > 38/55 := by linarith
    have h2 : (w.re - 17/55) * (w.re - 17/55) > 1444/3025 := by nlinarith
    linarith [h_sq_re]
  have h_mem : w.re ∈ Set.Icc (0 : ℝ) 1 := Set.mem_Icc.mpr ⟨h_ge_zero, h_le_one⟩
  exact ⟨hw_im, h_mem⟩

theorem z_of_w (z : ℂ) (w : ℂ) (h_sq : z^2 = w) (hw_im : w.im = 0) (hw_re_nonneg : 0 ≤ w.re) (hw_re_le_one : w.re ≤ 1) :
    z.im = 0 ∧ z.re ∈ Set.Icc (-1) 1 := by
  have h_sq_im : (z^2).im = w.im := by rw [h_sq]
  have h_sq_re : (z^2).re = w.re := by rw [h_sq]
  have h_sq_im2 : (z^2).im = 2 * z.re * z.im := by
    calc
      (z^2).im = (z * z).im := by rw [pow_two]
      _ = z.re * z.im + z.im * z.re := by simp [Complex.mul_im]
      _ = 2 * z.re * z.im := by ring
  have h_sq_re2 : (z^2).re = z.re^2 - z.im^2 := by
    calc
      (z^2).re = (z * z).re := by rw [pow_two]
      _ = z.re * z.re - z.im * z.im := by simp [Complex.mul_re]
      _ = z.re^2 - z.im^2 := by ring
  rw [hw_im] at h_sq_im
  rw [h_sq_im2] at h_sq_im
  have h_prod : z.re * z.im = 0 := by linarith
  cases mul_eq_zero.mp h_prod with
  | inr hz_im =>
    refine ⟨hz_im, ?_⟩
    rw [hz_im] at h_sq_re2
    simp at h_sq_re2
    rw [h_sq_re2] at h_sq_re
    -- z.re^2 = w.re
    have hz_re_sq_le : z.re^2 ≤ 1 := by linarith
    have hz_re_ge_neg_one : -1 ≤ z.re := by
      by_contra h_lt
      have : z.re^2 > 1 := by nlinarith
      linarith
    have hz_re_le_one : z.re ≤ 1 := by
      by_contra h_gt
      have : z.re^2 > 1 := by nlinarith
      linarith
    exact Set.mem_Icc.mpr ⟨hz_re_ge_neg_one, hz_re_le_one⟩
  | inl hz_re =>
    have hz_im_sq_le_zero : z.im^2 ≤ 0 := by
      calc
        z.im^2 = z.re^2 - w.re := by linarith [h_sq_re, h_sq_re2]
        _ = 0^2 - w.re := by rw [hz_re]
        _ = - w.re := by ring
        _ ≤ 0 := by linarith
    have hz_im_sq_ge_zero : 0 ≤ z.im^2 := sq_nonneg z.im
    have hz_im_sq_eq_zero : z.im^2 = 0 := by linarith
    have hz_im : z.im = 0 := sq_eq_zero_iff.mp hz_im_sq_eq_zero
    refine ⟨hz_im, ?_⟩
    rw [hz_re]
    simp [Set.mem_Icc]

theorem Q_1_roots (z : ℂ) (hz : (Q_1.map (algebraMap ℝ ℂ)).eval (z^2) = 0) :
    z.im = 0 ∧ z.re ∈ (Set.Icc (-1) 1) := by
  have h_map : (Q_1.map (algebraMap ℝ ℂ)).eval (z^2) = 220 * (z^2)^2 - 136 * (z^2) + 12 := by
    unfold Q_1
    simp [Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_ofNat]
  rw [hz] at h_map
  have h_roots_w := Q_1_roots_w (z^2) h_map.symm
  have hw_im : (z^2).im = 0 := h_roots_w.1
  have hw_re_mem : (z^2).re ∈ Set.Icc 0 1 := h_roots_w.2
  have hw_re_nonneg := (Set.mem_Icc.mp hw_re_mem).1
  have hw_re_le_one := (Set.mem_Icc.mp hw_re_mem).2
  exact z_of_w z (z^2) rfl hw_im hw_re_nonneg hw_re_le_one

theorem P_m_deg (m : ℕ) : (P_1 ^ m).degree = (2 * m : ℕ) := by
  rw [degree_pow, P_1_deg]
  simp
  ring

theorem Q_m_deg (m : ℕ) : (Q_1 ^ m).degree = (2 * m : ℕ) := by
  rw [degree_pow, Q_1_deg]
  simp
  ring

theorem P_m_sym (m : ℕ) (x : ℝ) : (P_1 ^ m).eval x = (P_1 ^ m).eval (1 - x) := by
  simp only [eval_pow]
  rw [P_1_sym]

theorem P_m_roots (m : ℕ) (hm : 1 ≤ m) (z : ℂ) (hz : ((P_1 ^ m).map (algebraMap ℝ ℂ)).eval z = 0) :
    z.im = 0 ∧ z.re ∈ Set.Icc 0 1 := by
  have h_pow : ((P_1 ^ m).map (algebraMap ℝ ℂ)).eval z = ((P_1.map (algebraMap ℝ ℂ)).eval z) ^ m := by
    simp [Polynomial.map_pow, eval_pow]
  rw [h_pow] at hz
  have hz2 : (P_1.map (algebraMap ℝ ℂ)).eval z = 0 := by
    exact eq_zero_of_pow_eq_zero hz
  exact P_1_roots z hz2

theorem Q_m_roots (m : ℕ) (hm : 1 ≤ m) (z : ℂ) (hz : ((Q_1 ^ m).map (algebraMap ℝ ℂ)).eval (z^2) = 0) :
    z.im = 0 ∧ z.re ∈ Set.Icc (-1) 1 := by
  have h_pow : ((Q_1 ^ m).map (algebraMap ℝ ℂ)).eval (z^2) = ((Q_1.map (algebraMap ℝ ℂ)).eval (z^2)) ^ m := by
    simp [Polynomial.map_pow, eval_pow]
  rw [h_pow] at hz
  have hz2 : (Q_1.map (algebraMap ℝ ℂ)).eval (z^2) = 0 := by
    exact eq_zero_of_pow_eq_zero hz
  exact Q_1_roots z hz2


/--
The recurrence given below can be rewritten in the form
(2*n+1)*(2*n+2)*P(2,n)*a(n+1) - (2*n-1)*(2*n-2)*P(2,-n)*a(n-1) = Q(2,n^2)*a(n), where the polynomial Q(2,n) = 4*(55*n^2 - 34*n + 3) and the polynomial P(2,n) = 5*n^2 - 5*n + 1 satisfies the symmetry condition P(2,n) = P(2,1-n) and has real zeros.
More generally, for fixed m = 1,2,3,..., we conjecture that the sequence b(n) := a(m*n) satisfies a recurrence of the form ( Product_{k = 1..2*m} (2*m*n + k) ) * P(2*m,n)*b(n+1) + (-1)^m*( Product_{k = 1..2*m} (2*m*n - k) ) * P(2*m,-n)*b(n-1) = Q(2*m,n^2)*b(n), where the polynomials P(2*m,n) and Q(2*m,n) have degree 2*m. Conjecturally, the polynomial P(2*m,n) = P(2*m,1-n) and has real zeros in the interval [0, 1]. The 4*m zeros of the polynomial Q(2*m,n^2) seem to belong to the interval [-1, 1] and 4*m - 2 of these zeros appear to be approximated by the rational numbers +- k/(3*m), where 1 <= k <= 3*m - 2, k not a multiple of 3.
-/
theorem oeis_a103885_conjecture_0 :
    (∀ (m : ℕ) (hm : 1 ≤ m),
    ∃ (P Q : Polynomial ℝ),
      -- P and Q have degree 2m
      P.degree = (2 * m : ℕ) ∧ Q.degree = (2 * m : ℕ) ∧
      -- The recurrence relation holds for all n >= 1
      (∀ (n : ℕ) (hn : 1 ≤ n),
        (prod_factor_plus m n * P.eval (n : ℝ)) * (A103885_subsequence_real m (n + 1)) +

        ((-1 : ℝ) ^ m * prod_factor_minus m n * P.eval (-(n : ℝ))) * (A103885_subsequence_real m (n - 1)) =

        (Q.eval ((n : ℝ)^2)) * (A103885_subsequence_real m n)) ∧

      -- P symmetry: P(x) = P(1-x)
      (∀ x : ℝ, P.eval x = P.eval (1 - x)) ∧

      -- P has real zeros in [0, 1]: all complex zeros are real and in [0, 1]
      (∀ z : ℂ, (P.map (algebraMap ℝ ℂ)).eval z = 0 → z.im = 0 ∧ z.re ∈ (Set.Icc 0 1)) ∧

      -- Q zero properties: The zeros of Q(x^2) are real and in [-1, 1].
      (∀ z : ℂ, (Q.map (algebraMap ℝ ℂ)).eval (z^2) = 0 → z.im = 0 ∧ z.re ∈ (Set.Icc (-1) 1))) := by
  intro m hm
  use P_1 ^ m, Q_1 ^ m
  refine ⟨P_m_deg m, Q_m_deg m, ?_, P_m_sym m, P_m_roots m hm, Q_m_roots m hm⟩
  intro n hn
  sorry
