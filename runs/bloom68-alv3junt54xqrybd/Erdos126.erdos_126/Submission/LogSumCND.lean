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
import FormalConjecturesUtil

/-!
# Conditional negative semidefiniteness of the logarithmic sum kernel

For any finite family of positive reals `a i`, the kernel
`(i, j) ↦ Real.log (a i + a j)` is conditionally negative semidefinite:
its quadratic form is nonpositive on real coefficients of sum zero.
The main theorem is `Erdos126Aux.log_sum_cnd`.

The proof uses `t i = (a i - 1) / (a i + 1)`, which has absolute value
less than one. The logarithmic kernel differs from `log (1 - t i * t j)`
only by row and column gauges. The power series for `-log (1 - x)` then
expresses the negative quadratic form as a convergent sum of squares;
see `Erdos126Aux.hasSum_neg_log_sum_quadratic`.

No result about polynomial prime support or any conjectural statement is used.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace Erdos126Aux

variable {ι : Type*} [Fintype ι]

/-- The negative quadratic form of `log (1 - t i * t j)` is a convergent
sum of squares whenever every `|t i|` is less than one. No zero-sum
assumption on the coefficients is needed for this kernel. -/
theorem hasSum_neg_log_one_sub_mul_quadratic (t c : ι → ℝ)
    (ht : ∀ i, |t i| < 1) :
    HasSum (fun n : ℕ => (∑ i, c i * t i ^ (n + 1)) ^ 2 / (n + 1))
      (-(∑ i, ∑ j, c i * c j * Real.log (1 - t i * t j))) := by
  classical
  have hprod (i j : ι) : |t i * t j| < 1 := by
    rw [abs_mul]
    exact mul_lt_one_of_nonneg_of_lt_one_left (abs_nonneg _) (ht i) (ht j).le
  have hs :
      HasSum
        (fun n : ℕ => ∑ i, ∑ j, c i * c j * ((t i * t j) ^ (n + 1) / (n + 1)))
        (∑ i, ∑ j, c i * c j * (-Real.log (1 - t i * t j))) :=
    hasSum_sum fun i _ => hasSum_sum fun j _ =>
      (Real.hasSum_pow_div_log_of_abs_lt_one (hprod i j)).mul_left (c i * c j)
  convert hs using 1
  · funext n
    rw [pow_two, Finset.sum_mul_sum, Finset.sum_div]
    simp_rw [Finset.sum_div, mul_pow]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  · simp only [mul_neg, Finset.sum_neg_distrib]

private theorem abs_cayley_lt_one {x : ℝ} (hx : 0 < x) :
    |(x - 1) / (x + 1)| < 1 := by
  have hx1 : 0 < x + 1 := by linarith
  rw [abs_lt]
  constructor
  · apply (lt_div_iff₀ hx1).2
    linarith
  · apply (div_lt_one hx1).2
    linarith

private theorem log_add_eq_gauges {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    Real.log (x + y) =
      (Real.log (x + 1) - Real.log 2) + Real.log (y + 1) +
        Real.log (1 - ((x - 1) / (x + 1)) * ((y - 1) / (y + 1))) := by
  have hx1 : 0 < x + 1 := by linarith
  have hy1 : 0 < y + 1 := by linarith
  have hprod : |((x - 1) / (x + 1)) * ((y - 1) / (y + 1))| < 1 := by
    rw [abs_mul]
    exact mul_lt_one_of_nonneg_of_lt_one_left (abs_nonneg _)
      (abs_cayley_lt_one hx) (abs_cayley_lt_one hy).le
  have hfactor :
      0 < 1 - ((x - 1) / (x + 1)) * ((y - 1) / (y + 1)) := by
    have := (le_abs_self _).trans_lt hprod
    linarith
  have hid : x + y = ((x + 1) * (y + 1) / 2) *
      (1 - ((x - 1) / (x + 1)) * ((y - 1) / (y + 1))) := by
    field_simp [ne_of_gt hx1, ne_of_gt hy1]
    ring
  rw [hid, Real.log_mul (ne_of_gt (div_pos (mul_pos hx1 hy1) (by norm_num)))
    (ne_of_gt hfactor), Real.log_div (ne_of_gt (mul_pos hx1 hy1)) (by norm_num),
    Real.log_mul (ne_of_gt hx1) (ne_of_gt hy1)]
  ring

private theorem quadratic_gauges_cancel (c r s : ι → ℝ) (K : ι → ι → ℝ)
    (hc : ∑ i, c i = 0) :
    (∑ i, ∑ j, c i * c j * (r i + s j + K i j)) =
      ∑ i, ∑ j, c i * c j * K i j := by
  classical
  have hrow : (∑ i, ∑ j, c i * c j * r i) = 0 := by
    calc
      _ = ∑ i, (c i * r i) * (∑ j, c j) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = 0 := by simp [hc]
  have hcol : (∑ i, ∑ j, c i * c j * s j) = 0 := by
    calc
      _ = (∑ i, c i) * (∑ j, c j * s j) := by
        rw [Finset.sum_mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = 0 := by rw [hc, zero_mul]
  simp_rw [mul_add, Finset.sum_add_distrib]
  rw [hrow, hcol]
  simp

/-- Sum-of-squares certificate for the logarithmic sum kernel on coefficients
of sum zero. The series starts with exponent one, so every denominator is positive. -/
theorem hasSum_neg_log_sum_quadratic (a c : ι → ℝ)
    (ha : ∀ i, 0 < a i) (hc : ∑ i, c i = 0) :
    HasSum
      (fun n : ℕ => (∑ i, c i * ((a i - 1) / (a i + 1)) ^ (n + 1)) ^ 2 / (n + 1))
      (-(∑ i, ∑ j, c i * c j * Real.log (a i + a j))) := by
  have hgauge :
      (∑ i, ∑ j, c i * c j * Real.log (a i + a j)) =
        ∑ i, ∑ j, c i * c j *
          Real.log (1 - ((a i - 1) / (a i + 1)) * ((a j - 1) / (a j + 1))) := by
    calc
      _ = ∑ i, ∑ j, c i * c j *
          ((Real.log (a i + 1) - Real.log 2) + Real.log (a j + 1) +
            Real.log (1 - ((a i - 1) / (a i + 1)) * ((a j - 1) / (a j + 1)))) := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        rw [log_add_eq_gauges (ha i) (ha j)]
      _ = _ := quadratic_gauges_cancel c (fun i => Real.log (a i + 1) - Real.log 2)
        (fun j => Real.log (a j + 1)) _ hc
  rw [hgauge]
  exact hasSum_neg_log_one_sub_mul_quadratic (fun i => (a i - 1) / (a i + 1)) c
    (fun i => abs_cayley_lt_one (ha i))

/-- For any finite family of positive reals, the matrix `log (a i + a j)`
is conditionally negative semidefinite: its quadratic form is nonpositive
on real coefficients whose sum is zero. The family need not be distinct. -/
theorem log_sum_cnd (a c : ι → ℝ) (ha : ∀ i, 0 < a i) (hc : ∑ i, c i = 0) :
    (∑ i, ∑ j, c i * c j * Real.log (a i + a j)) ≤ 0 := by
  have hnonneg := (hasSum_neg_log_sum_quadratic a c ha hc).nonneg
    (fun n => div_nonneg (sq_nonneg _) (by positivity))
  linarith

end Erdos126Aux
