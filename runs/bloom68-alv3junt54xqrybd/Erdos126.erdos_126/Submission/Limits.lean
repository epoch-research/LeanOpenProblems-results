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
import Submission.Extremal

/-!
# Asymptotic reductions for Erdős problem 126

The divergence of `extremal n / log n` is equivalent to a uniform eventual
lower bound for the prime support of every finite set. It is also equivalent
to a uniform subexponential inequality with an additive constant.

These are only reductions: no subexponential estimate or asymptotic conclusion
is assumed or proved unconditionally. The final lemmas transfer the reductions
to any function with the greatest-bound property, using uniqueness from
`Submission.Extremal`. This file does not import `Submission.Spec`.
-/

open Filter

namespace Erdos126Aux

/-- The logarithm of a natural number is positive once the number is at least two. -/
theorem log_natCast_pos_of_two_le {n : ℕ} (hn : 2 ≤ n) :
    0 < Real.log (n : ℝ) := by
  apply Real.log_pos
  exact_mod_cast (show 1 < n by omega)

/-- The logarithm of the natural-number argument tends to positive infinity. -/
theorem tendsto_log_natCast_atTop :
    Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

/-- Divergence of the extremal ratio is exactly the uniform eventual prime-count
lower bound. Thresholds may be increased to two, so every division is by a
strictly positive logarithm. -/
theorem tendsto_extremal_div_log_iff_uniform_lower_bound :
    Tendsto (fun n : ℕ => (extremal n : ℝ) / Real.log (n : ℝ)) atTop atTop ↔
      ∀ K : ℝ, ∃ N : ℕ, ∀ A : Finset ℕ, N ≤ A.card →
        K * Real.log (A.card : ℝ) ≤ (supportCount A : ℝ) := by
  constructor
  · intro h K
    obtain ⟨N, hN⟩ := tendsto_atTop_atTop.mp h K
    refine ⟨max N 2, ?_⟩
    intro A hA
    have htwo : 2 ≤ A.card := (le_max_right N 2).trans hA
    have hlarge : N ≤ A.card := (le_max_left N 2).trans hA
    exact ((le_div_iff₀ (log_natCast_pos_of_two_le htwo)).mp (hN A.card hlarge)).trans
      (Nat.cast_le.mpr (extremal_le_supportCount rfl))
  · intro h
    apply tendsto_atTop_atTop.mpr
    intro K
    obtain ⟨N, hN⟩ := h K
    refine ⟨max N 2, ?_⟩
    intro n hn
    have htwo : 2 ≤ n := (le_max_right N 2).trans hn
    have hlarge : N ≤ n := (le_max_left N 2).trans hn
    obtain ⟨A, hcard, hmin⟩ := extremal_attained n
    apply (le_div_iff₀ (log_natCast_pos_of_two_le htwo)).mpr
    simpa only [hcard, hmin] using hN A (by simpa only [hcard] using hlarge)

/-- A uniform subexponential inequality implies the uniform eventual lower bound.
For a requested slope `K`, use `ε = 1 / (max K 0 + 1)` and absorb the additive
constant using the divergence of `log n`. -/
theorem uniform_lower_bound_of_subexponential_bound
    (h : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ A : Finset ℕ, 2 ≤ A.card →
      Real.log (A.card : ℝ) ≤ C + ε * (supportCount A : ℝ)) :
    ∀ K : ℝ, ∃ N : ℕ, ∀ A : Finset ℕ, N ≤ A.card →
      K * Real.log (A.card : ℝ) ≤ (supportCount A : ℝ) := by
  intro K
  let B : ℝ := max K 0
  have hB : 0 ≤ B := le_max_right K 0
  have hKB : K ≤ B := le_max_left K 0
  have hBpos : 0 < B + 1 := by linarith
  obtain ⟨C, hC⟩ := h (1 / (B + 1)) (one_div_pos.mpr hBpos)
  obtain ⟨N, hN⟩ := tendsto_atTop_atTop.mp tendsto_log_natCast_atTop ((B + 1) * C)
  refine ⟨max N 2, ?_⟩
  intro A hA
  have htwo : 2 ≤ A.card := (le_max_right N 2).trans hA
  have hlarge : N ≤ A.card := (le_max_left N 2).trans hA
  have hlog : 0 ≤ Real.log (A.card : ℝ) := (log_natCast_pos_of_two_le htwo).le
  have hconstant := hN A.card hlarge
  have hscaled := mul_le_mul_of_nonneg_left (hC A htwo) hBpos.le
  have hcancel : (B + 1) * (1 / (B + 1)) = 1 :=
    mul_one_div_cancel (ne_of_gt hBpos)
  rw [mul_add, ← mul_assoc, hcancel, one_mul] at hscaled
  have hsupport : B * Real.log (A.card : ℝ) ≤ (supportCount A : ℝ) := by
    nlinarith
  exact (mul_le_mul_of_nonneg_right hKB hlog).trans hsupport

/-- Conversely, the uniform eventual lower bound gives a subexponential inequality.
The finitely many smaller cardinalities are covered by the additive constant `N`. -/
theorem subexponential_bound_of_uniform_lower_bound
    (h : ∀ K : ℝ, ∃ N : ℕ, ∀ A : Finset ℕ, N ≤ A.card →
      K * Real.log (A.card : ℝ) ≤ (supportCount A : ℝ)) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ A : Finset ℕ, 2 ≤ A.card →
      Real.log (A.card : ℝ) ≤ C + ε * (supportCount A : ℝ) := by
  intro ε hε
  obtain ⟨N, hN⟩ := h (1 / ε)
  refine ⟨(N : ℝ), ?_⟩
  intro A _htwo
  have hNnonneg : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hsnonneg : 0 ≤ ε * (supportCount A : ℝ) :=
    mul_nonneg hε.le (Nat.cast_nonneg _)
  by_cases hlarge : N ≤ A.card
  · have hscaled := mul_le_mul_of_nonneg_left (hN A hlarge) hε.le
    rw [← mul_assoc, mul_one_div_cancel (ne_of_gt hε), one_mul] at hscaled
    linarith
  · have hcard : (A.card : ℝ) ≤ N := Nat.cast_le.mpr (le_of_lt (lt_of_not_ge hlarge))
    exact (Real.log_le_self (Nat.cast_nonneg A.card)).trans (by linarith)

/-- The two uniform forms of the asymptotic condition are equivalent. -/
theorem uniform_lower_bound_iff_subexponential_bound :
    (∀ K : ℝ, ∃ N : ℕ, ∀ A : Finset ℕ, N ≤ A.card →
      K * Real.log (A.card : ℝ) ≤ (supportCount A : ℝ)) ↔
    (∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ A : Finset ℕ, 2 ≤ A.card →
      Real.log (A.card : ℝ) ≤ C + ε * (supportCount A : ℝ)) :=
  ⟨subexponential_bound_of_uniform_lower_bound, uniform_lower_bound_of_subexponential_bound⟩

/-- The requested ratio divergence is equivalent to the subexponential inequality. -/
theorem tendsto_extremal_div_log_iff_subexponential_bound :
    Tendsto (fun n : ℕ => (extremal n : ℝ) / Real.log (n : ℝ)) atTop atTop ↔
      ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ A : Finset ℕ, 2 ≤ A.card →
        Real.log (A.card : ℝ) ≤ C + ε * (supportCount A : ℝ) :=
  tendsto_extremal_div_log_iff_uniform_lower_bound.trans
    uniform_lower_bound_iff_subexponential_bound

/-- A future proof of the subexponential inequality immediately gives the target limit. -/
theorem tendsto_extremal_div_log_of_subexponential_bound
    (h : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ A : Finset ℕ, 2 ≤ A.card →
      Real.log (A.card : ℝ) ≤ C + ε * (supportCount A : ℝ)) :
    Tendsto (fun n : ℕ => (extremal n : ℝ) / Real.log (n : ℝ)) atTop atTop :=
  tendsto_extremal_div_log_iff_subexponential_bound.mpr h

/-- Transfer the uniform lower-bound characterization to any greatest-bound function. -/
theorem tendsto_div_log_iff_uniform_lower_bound_of_isGreatest {f : ℕ → ℕ}
    (hf : ∀ n,
      IsGreatest {m : ℕ | ∀ A : Finset ℕ, A.card = n → m ≤ supportCount A} (f n)) :
    Tendsto (fun n : ℕ => (f n : ℝ) / Real.log (n : ℝ)) atTop atTop ↔
      ∀ K : ℝ, ∃ N : ℕ, ∀ A : Finset ℕ, N ≤ A.card →
        K * Real.log (A.card : ℝ) ≤ (supportCount A : ℝ) := by
  rw [eq_extremal_of_isGreatest hf]
  exact tendsto_extremal_div_log_iff_uniform_lower_bound

/-- Transfer the subexponential characterization to any greatest-bound function. -/
theorem tendsto_div_log_iff_subexponential_bound_of_isGreatest {f : ℕ → ℕ}
    (hf : ∀ n,
      IsGreatest {m : ℕ | ∀ A : Finset ℕ, A.card = n → m ≤ supportCount A} (f n)) :
    Tendsto (fun n : ℕ => (f n : ℝ) / Real.log (n : ℝ)) atTop atTop ↔
      ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ A : Finset ℕ, 2 ≤ A.card →
        Real.log (A.card : ℝ) ≤ C + ε * (supportCount A : ℝ) :=
  (tendsto_div_log_iff_uniform_lower_bound_of_isGreatest hf).trans
    uniform_lower_bound_iff_subexponential_bound

/-- A reusable implication for the function in the original greatest-bound formulation. -/
theorem tendsto_div_log_of_subexponential_bound_of_isGreatest {f : ℕ → ℕ}
    (hf : ∀ n,
      IsGreatest {m : ℕ | ∀ A : Finset ℕ, A.card = n → m ≤ supportCount A} (f n))
    (h : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ A : Finset ℕ, 2 ≤ A.card →
      Real.log (A.card : ℝ) ≤ C + ε * (supportCount A : ℝ)) :
    Tendsto (fun n : ℕ => (f n : ℝ) / Real.log (n : ℝ)) atTop atTop :=
  (tendsto_div_log_iff_subexponential_bound_of_isGreatest hf).mpr h

end Erdos126Aux
