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
import Submission.LogSumCND
import Submission.PairedCore

/-!
# Valuation and logarithmic baselines for positive natural sums

Valuations are represented by `Nat.factorization`.  The prime baseline is
`min` of the two heights, together with the equal-height contribution at
2.  Its positive semidefiniteness comes from finite threshold and height
outer products.  Exact logarithmic factorization and its restricted-sum
version account for prime factors outside a chosen finite set, including
those occurring only on the diagonal.

This file does not construct paired residue blocks and does not use a
conjectural prime-support bound.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace Erdos126Aux

/- ## Elementary valuation identities -/

/-- The smaller of two prime heights is a lower bound for the height of
 their positive natural sum. -/
theorem min_factorization_le_factorization_add {p a b : ℕ} (hp : p.Prime)
    (ha : 0 < a) (hb : 0 < b) :
    min (a.factorization p) (b.factorization p) ≤ (a + b).factorization p := by
  apply (hp.pow_dvd_iff_le_factorization (Nat.ne_of_gt (add_pos ha hb))).1
  exact dvd_add
    ((hp.pow_dvd_iff_le_factorization ha.ne').2 (min_le_left _ _))
    ((hp.pow_dvd_iff_le_factorization hb.ne').2 (min_le_right _ _))

/-- If the first prime height is strictly smaller, it is exactly the
 height of the sum. -/
theorem factorization_add_eq_left_of_lt {p a b : ℕ} (hp : p.Prime)
    (ha : 0 < a) (hb : 0 < b)
    (h : a.factorization p < b.factorization p) :
    (a + b).factorization p = a.factorization p := by
  have hlo := min_factorization_le_factorization_add hp ha hb
  rw [min_eq_left h.le] at hlo
  have hnot : ¬p ^ (a.factorization p + 1) ∣ a + b := by
    have hdb : p ^ (a.factorization p + 1) ∣ b :=
      (hp.pow_dvd_iff_le_factorization hb.ne').2 (Nat.add_one_le_iff.2 h)
    exact fun hd => Nat.pow_succ_factorization_not_dvd ha.ne' hp
      ((Nat.dvd_add_iff_left hdb).2 hd)
  have hhi : (a + b).factorization p ≤ a.factorization p := by
    by_contra hhi
    exact hnot ((hp.pow_dvd_iff_le_factorization
      (Nat.ne_of_gt (add_pos ha hb))).2 (by omega))
  exact Nat.le_antisymm hhi hlo

/-- Unequal prime heights do not cancel in a positive natural sum. -/
theorem factorization_add_eq_min_of_ne {p a b : ℕ} (hp : p.Prime)
    (ha : 0 < a) (hb : 0 < b)
    (h : a.factorization p ≠ b.factorization p) :
    (a + b).factorization p = min (a.factorization p) (b.factorization p) := by
  rcases lt_or_gt_of_ne h with hlt | hgt
  · rw [factorization_add_eq_left_of_lt hp ha hb hlt, min_eq_left hlt.le]
  · rw [add_comm, factorization_add_eq_left_of_lt hp hb ha hgt,
      min_eq_right hgt.le]

/-- Equal 2-adic heights acquire at least one additional factor of 2
 when the positive summands are added. -/
theorem factorization_two_add_ge_of_eq {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (h : a.factorization 2 = b.factorization 2) :
    a.factorization 2 + 1 ≤ (a + b).factorization 2 := by
  let u := a / 2 ^ a.factorization 2
  let v := b / 2 ^ b.factorization 2
  have hu : Odd u := Nat.not_even_iff_odd.1
    (fun he => Nat.not_dvd_ordCompl Nat.prime_two ha.ne' he.two_dvd)
  have hv : Odd v := Nat.not_even_iff_odd.1
    (fun he => Nat.not_dvd_ordCompl Nat.prime_two hb.ne' he.two_dvd)
  have heq : a + b = 2 ^ a.factorization 2 * (u + v) := by
    calc
      a + b = 2 ^ a.factorization 2 * u + 2 ^ b.factorization 2 * v := by
        rw [Nat.ordProj_mul_ordCompl_eq_self, Nat.ordProj_mul_ordCompl_eq_self]
      _ = _ := by rw [h, mul_add]
  apply (Nat.prime_two.pow_dvd_iff_le_factorization
    (Nat.ne_of_gt (add_pos ha hb))).1
  rw [heq, pow_succ]
  exact mul_dvd_mul_left _ (hu.add_odd hv).two_dvd

/-- The valuation on a doubled positive natural number.  The statement
 holds at every natural `p`, with no primality assumption. -/
theorem factorization_two_mul {p a : ℕ} (ha : 0 < a) :
    (2 * a).factorization p = a.factorization p + (if p = 2 then 1 else 0) := by
  rw [Nat.factorization_mul (by decide) ha.ne', Finsupp.add_apply,
    Nat.prime_two.factorization]
  simp [Finsupp.single_apply, eq_comm, add_comm]

/- ## Exact logarithmic factorization and finite restrictions -/

/-- Exact prime-factor logarithmic expansion.  This also holds at 0 by
 Mathlib's conventions, so no positivity hypothesis is necessary. -/
theorem log_nat_eq_sum_primeFactors (n : ℕ) :
    Real.log (n : ℝ) =
      ∑ p ∈ n.primeFactors, (n.factorization p : ℝ) * Real.log (p : ℝ) := by
  simpa only [Finsupp.sum, Nat.support_factorization] using
    Real.log_nat_eq_sum_factorization n

/-- The factorization/log summand is nonnegative even when `p` is not
 prime (its height is then zero). -/
theorem factorization_mul_log_nonneg (n p : ℕ) :
    0 ≤ (n.factorization p : ℝ) * Real.log (p : ℝ) :=
  mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg _)

/-- All nonzero factorization summands are accounted for once the finite
 set contains the prime factors.  Extra primes, or nonprimes, are harmless. -/
theorem sum_factorization_log_eq_log_of_subset (n : ℕ) (S : Finset ℕ)
    (h : n.primeFactors ⊆ S) :
    (∑ p ∈ S, (n.factorization p : ℝ) * Real.log (p : ℝ)) = Real.log (n : ℝ) := by
  rw [log_nat_eq_sum_primeFactors]
  symm
  apply Finset.sum_subset h
  intro p _ hp
  have hzero : n.factorization p = 0 :=
    Finsupp.notMem_support_iff.1 (by simpa only [Nat.support_factorization] using hp)
  simp [hzero]

/-- Restricting logarithmic prime factorization to any finite set can
 only decrease the sum. -/
theorem sum_factorization_log_le_log (n : ℕ) (S : Finset ℕ) :
    (∑ p ∈ S, (n.factorization p : ℝ) * Real.log (p : ℝ)) ≤ Real.log (n : ℝ) := by
  calc
    _ ≤ ∑ p ∈ S ∪ n.primeFactors, (n.factorization p : ℝ) * Real.log (p : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
        (fun p _ _ => factorization_mul_log_nonneg n p)
    _ = _ := sum_factorization_log_eq_log_of_subset n _ Finset.subset_union_right

/-- The finite logarithmic mass from prime factors outside `S`. -/
noncomputable def outsidePrimeLog (S : Finset ℕ) (n : ℕ) : ℝ :=
  ∑ p ∈ n.primeFactors \ S, (n.factorization p : ℝ) * Real.log (p : ℝ)

theorem outsidePrimeLog_nonneg (S : Finset ℕ) (n : ℕ) :
    0 ≤ outsidePrimeLog S n := by
  exact Finset.sum_nonneg (fun p _ => factorization_mul_log_nonneg n p)

/-- Exact restricted factorization plus the finite outside-support mass. -/
theorem sum_factorization_log_add_outside (S : Finset ℕ) (n : ℕ) :
    (∑ p ∈ S, (n.factorization p : ℝ) * Real.log (p : ℝ)) + outsidePrimeLog S n =
      Real.log (n : ℝ) := by
  have hs := Finset.sum_sdiff (f := fun p =>
    (n.factorization p : ℝ) * Real.log (p : ℝ))
    (Finset.subset_union_left : S ⊆ S ∪ n.primeFactors)
  have hset : (S ∪ n.primeFactors) \ S = n.primeFactors \ S := by
    ext p
    simp only [Finset.mem_sdiff, Finset.mem_union]
    tauto
  rw [hset, sum_factorization_log_eq_log_of_subset n _ Finset.subset_union_right] at hs
  simpa only [outsidePrimeLog, add_comm] using hs

/-- The outside mass vanishes when the prime factors are included. -/
theorem outsidePrimeLog_eq_zero_of_subset (S : Finset ℕ) (n : ℕ)
    (h : n.primeFactors ⊆ S) : outsidePrimeLog S n = 0 := by
  simp only [outsidePrimeLog, Finset.sdiff_eq_empty_iff_subset.mpr h, Finset.sum_empty]


/- ## Finite threshold and height outer products -/

variable {ι : Type*}

/-- Indicator of the strict height threshold `k < h i`. -/
noncomputable def heightThreshold (h : ι → ℕ) (k : ℕ) (i : ι) : ℝ :=
  if k < h i then 1 else 0

/-- Indicator of a single height class. -/
noncomputable def heightIndicator (h : ι → ℕ) (k : ℕ) (i : ι) : ℝ :=
  if h i = k then 1 else 0

noncomputable def minHeightKernel (h : ι → ℕ) (i j : ι) : ℝ :=
  (min (h i) (h j) : ℕ)

noncomputable def equalHeightKernel (h : ι → ℕ) (i j : ι) : ℝ :=
  if h i = h j then 1 else 0

/-- Finite threshold outer-product decomposition of the minimum kernel. -/
theorem minHeightKernel_eq_sum_thresholds (h : ι → ℕ) (N : ℕ)
    (hN : ∀ i, h i ≤ N) (i j : ι) :
    minHeightKernel h i j =
      ∑ k ∈ Finset.range N, heightThreshold h k i * heightThreshold h k j := by
  have hfilter : (Finset.range N).filter (fun k => k < h i ∧ k < h j) =
      Finset.range (min (h i) (h j)) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, lt_min_iff]
    have hi := hN i
    have hj := hN j
    omega
  calc
    minHeightKernel h i j =
        ∑ k ∈ Finset.range N, if k < h i ∧ k < h j then (1 : ℝ) else 0 := by
      rw [Finset.sum_boole, hfilter]
      simp [minHeightKernel]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k _
      unfold heightThreshold
      split_ifs <;> simp_all

/-- Finite height-class outer-product decomposition of the equal-height
 kernel.  The range includes height zero. -/
theorem equalHeightKernel_eq_sum_heightIndicators (h : ι → ℕ) (N : ℕ)
    (hN : ∀ i, h i ≤ N) (i j : ι) :
    equalHeightKernel h i j =
      ∑ k ∈ Finset.range (N + 1), heightIndicator h k i * heightIndicator h k j := by
  by_cases hij : h i = h j
  · have hj : h j < N + 1 := by have := hN j; omega
    simp [equalHeightKernel, heightIndicator, hij, eq_comm, hj]
  · simp only [equalHeightKernel, hij, if_false]
    symm
    apply Finset.sum_eq_zero
    intro k _
    unfold heightIndicator
    split_ifs <;> simp_all

/-- The real-valued unweighted prime baseline, including the 2-adic
 equal-height term. -/
noncomputable def primeBaseline (a : ι → ℕ) (p : ℕ) (i j : ι) : ℝ :=
  (min ((a i).factorization p) ((a j).factorization p) : ℕ) +
    (if p = 2 ∧ (a i).factorization p = (a j).factorization p then 1 else 0)

theorem primeBaseline_symm (a : ι → ℕ) (p : ℕ) (i j : ι) :
    primeBaseline a p i j = primeBaseline a p j i := by
  simp [primeBaseline, min_comm, eq_comm]

/-- Unequal heights have no equal-height baseline contribution. -/
theorem primeBaseline_eq_min_of_ne (a : ι → ℕ) (p : ℕ) (i j : ι)
    (h : (a i).factorization p ≠ (a j).factorization p) :
    primeBaseline a p i j =
      ((min ((a i).factorization p) ((a j).factorization p) : ℕ) : ℝ) := by
  simp [primeBaseline, h]

/-- With unequal heights, the entire sum valuation is baseline. -/
theorem primeBaseline_eq_factorization_add_of_ne (a : ι → ℕ) {p : ℕ} (hp : p.Prime)
    (i j : ι) (hi : 0 < a i) (hj : 0 < a j)
    (h : (a i).factorization p ≠ (a j).factorization p) :
    primeBaseline a p i j = ((a i + a j).factorization p : ℝ) := by
  rw [primeBaseline_eq_min_of_ne a p i j h,
    factorization_add_eq_min_of_ne hp hi hj h]

/-- The baseline accounts for the entire valuation on the diagonal. -/
theorem primeBaseline_diagonal (a : ι → ℕ) (p : ℕ) (i : ι) (ha : 0 < a i) :
    primeBaseline a p i i = ((2 * a i).factorization p : ℝ) := by
  rw [factorization_two_mul ha]
  simp only [primeBaseline, min_self, and_true, Nat.cast_add]
  split_ifs <;> simp

/-- The baseline is an entrywise lower bound for the valuation of a
 positive natural sum. -/
theorem primeBaseline_le_factorization_add (a : ι → ℕ) {p : ℕ} (hp : p.Prime)
    (i j : ι) (hi : 0 < a i) (hj : 0 < a j) :
    primeBaseline a p i j ≤ ((a i + a j).factorization p : ℝ) := by
  by_cases hp2 : p = 2
  · subst p
    by_cases heq : (a i).factorization 2 = (a j).factorization 2
    · simp only [primeBaseline, ← heq, min_self, and_self, if_true]
      exact_mod_cast factorization_two_add_ge_of_eq hi hj heq
    · simp only [primeBaseline, heq, and_false, if_false, add_zero]
      exact_mod_cast min_factorization_le_factorization_add hp hi hj
  · simp only [primeBaseline, hp2, false_and, if_false, add_zero]
    exact_mod_cast min_factorization_le_factorization_add hp hi hj

section QuadraticForms

variable [Fintype ι]

private theorem valuation_qform_finset_sum {τ : Type*} (T : Finset τ)
    (K : τ → ι → ι → ℝ) (x : ι → ℝ) :
    Paired.qform (fun i j => ∑ t ∈ T, K t i j) x =
      ∑ t ∈ T, Paired.qform (K t) x := by
  unfold Paired.qform
  simp_rw [Finset.mul_sum]
  calc
    (∑ i, ∑ j, ∑ t ∈ T, x i * x j * K t i j) =
        ∑ i, ∑ t ∈ T, ∑ j, x i * x j * K t i j := by
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ t ∈ T, ∑ i, ∑ j, x i * x j * K t i j := Finset.sum_comm

private theorem valuation_qform_outer (v x : ι → ℝ) :
    Paired.qform (fun i j => v i * v j) x = (∑ i, x i * v i) ^ 2 := by
  unfold Paired.qform
  rw [pow_two, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem valuation_qform_smul (r : ℝ) (K : ι → ι → ℝ) (x : ι → ℝ) :
    Paired.qform (fun i j => r * K i j) x = r * Paired.qform K x := by
  unfold Paired.qform
  simp_rw [show ∀ i j, x i * x j * (r * K i j) = r * (x i * x j * K i j) by
    intros; ring]
  simp_rw [← Finset.mul_sum]

/-- Explicit finite sum-of-squares certificate for the minimum kernel. -/
theorem minHeightKernel_qform (h : ι → ℕ) (N : ℕ) (hN : ∀ i, h i ≤ N)
    (x : ι → ℝ) :
    Paired.qform (minHeightKernel h) x =
      ∑ k ∈ Finset.range N, (∑ i, x i * heightThreshold h k i) ^ 2 := by
  have he : minHeightKernel h =
      (fun i j => ∑ k ∈ Finset.range N, heightThreshold h k i * heightThreshold h k j) :=
    funext fun i => funext fun j => minHeightKernel_eq_sum_thresholds h N hN i j
  rw [he, valuation_qform_finset_sum]
  simp_rw [valuation_qform_outer]

/-- Explicit finite sum-of-squares certificate for the equal-height kernel. -/
theorem equalHeightKernel_qform (h : ι → ℕ) (N : ℕ) (hN : ∀ i, h i ≤ N)
    (x : ι → ℝ) :
    Paired.qform (equalHeightKernel h) x =
      ∑ k ∈ Finset.range (N + 1), (∑ i, x i * heightIndicator h k i) ^ 2 := by
  have he : equalHeightKernel h =
      (fun i j => ∑ k ∈ Finset.range (N + 1),
        heightIndicator h k i * heightIndicator h k j) :=
    funext fun i => funext fun j => equalHeightKernel_eq_sum_heightIndicators h N hN i j
  rw [he, valuation_qform_finset_sum]
  simp_rw [valuation_qform_outer]

/-- Minimum of nonnegative integer heights is a PSD kernel on a finite
 family; neither positivity of the heights nor a nonempty index type is needed. -/
theorem minHeightKernel_psd (h : ι → ℕ) : Paired.PSD (minHeightKernel h) := by
  classical
  intro x
  rw [minHeightKernel_qform h (Finset.univ.sup h)
    (fun i => Finset.le_sup (Finset.mem_univ i))]
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem equalHeightKernel_psd (h : ι → ℕ) : Paired.PSD (equalHeightKernel h) := by
  classical
  intro x
  rw [equalHeightKernel_qform h (Finset.univ.sup h)
    (fun i => Finset.le_sup (Finset.mem_univ i))]
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- The prime baseline is PSD.  In fact this holds for arbitrary natural
 `p` and arbitrary natural families, even with zero entries. -/
theorem primeBaseline_psd (a : ι → ℕ) (p : ℕ) : Paired.PSD (primeBaseline a p) := by
  let h : ι → ℕ := fun i => (a i).factorization p
  intro x
  have hmin := minHeightKernel_psd h x
  have heq := equalHeightKernel_psd h x
  by_cases hp : p = 2
  · have he : primeBaseline a p =
        (fun i j => minHeightKernel h i j + equalHeightKernel h i j) := by
      funext i j
      simp only [primeBaseline, minHeightKernel, equalHeightKernel, hp, true_and, h]
    rw [he]
    simp only [Paired.qform, mul_add, Finset.sum_add_distrib] at *
    exact add_nonneg hmin heq
  · have he : primeBaseline a p = minHeightKernel h := by
      funext i j
      simp only [primeBaseline, minHeightKernel, hp, false_and, if_false, add_zero, h]
    rw [he]
    exact hmin

/-- The finite logarithm-weighted sum of the prime baselines. -/
noncomputable def primeBaselineSum (a : ι → ℕ) (S : Finset ℕ) (i j : ι) : ℝ :=
  ∑ p ∈ S, Real.log (p : ℝ) * primeBaseline a p i j

/-- Logarithm-weighted baseline sums are PSD.  No primality condition on
 `S` is necessary, since natural logarithmic weights are nonnegative. -/
theorem primeBaselineSum_psd (a : ι → ℕ) (S : Finset ℕ) :
    Paired.PSD (primeBaselineSum a S) := by
  intro x
  unfold primeBaselineSum
  rw [valuation_qform_finset_sum]
  apply Finset.sum_nonneg
  intro p _
  rw [valuation_qform_smul]
  exact mul_nonneg (Real.log_natCast_nonneg p) (primeBaseline_psd a p x)

end QuadraticForms

/- ## Outside-support diagonal and active kernels -/

/-- A diagonal real kernel; equality is decided classically inside the definition. -/
noncomputable def diagonalKernel (d : ι → ℝ) (i j : ι) : ℝ := by
  classical
  exact if i = j then d i else 0

noncomputable def outsidePrimeDiagonal (a : ι → ℕ) (S : Finset ℕ) : ι → ι → ℝ :=
  diagonalKernel (fun i => outsidePrimeLog S (2 * a i))

/-- Logarithmic sum kernel with the weighted prime baselines and the
 outside-support diagonal removed. -/
noncomputable def logActiveKernel (a : ι → ℕ) (S : Finset ℕ) (i j : ι) : ℝ :=
  Real.log ((a i : ℝ) + (a j : ℝ)) - primeBaselineSum a S i j -
    outsidePrimeDiagonal a S i j

/-- The finite prime sum of valuation excess above the baselines. -/
noncomputable def primeExcessKernel (a : ι → ℕ) (S : Finset ℕ) (i j : ι) : ℝ :=
  ∑ p ∈ S, Real.log (p : ℝ) *
    (((a i + a j).factorization p : ℝ) - primeBaseline a p i j)

theorem diagonalKernel_symm (d : ι → ℝ) (i j : ι) :
    diagonalKernel d i j = diagonalKernel d j i := by
  classical
  by_cases hij : i = j
  · subst j
    rfl
  · simp [diagonalKernel, hij, Ne.symm hij]

theorem primeBaselineSum_symm (a : ι → ℕ) (S : Finset ℕ) (i j : ι) :
    primeBaselineSum a S i j = primeBaselineSum a S j i := by
  unfold primeBaselineSum
  apply Finset.sum_congr rfl
  intro p _
  rw [primeBaseline_symm]

theorem primeBaselineSum_diagonal (a : ι → ℕ) (S : Finset ℕ) (i : ι)
    (ha : 0 < a i) :
    primeBaselineSum a S i i =
      ∑ p ∈ S, ((2 * a i).factorization p : ℝ) * Real.log (p : ℝ) := by
  unfold primeBaselineSum
  apply Finset.sum_congr rfl
  intro p _
  rw [primeBaseline_diagonal a p i ha, mul_comm]

theorem logActiveKernel_symm (a : ι → ℕ) (S : Finset ℕ) (i j : ι) :
    logActiveKernel a S i j = logActiveKernel a S j i := by
  unfold logActiveKernel outsidePrimeDiagonal
  rw [add_comm, primeBaselineSum_symm, diagonalKernel_symm]

theorem primeExcessKernel_symm (a : ι → ℕ) (S : Finset ℕ) (i j : ι) :
    primeExcessKernel a S i j = primeExcessKernel a S j i := by
  unfold primeExcessKernel
  apply Finset.sum_congr rfl
  intro p _
  rw [add_comm, primeBaseline_symm]

/-- The removed diagonal accounts for every outside-support prime, so
 the active logarithmic kernel has exactly zero diagonal. -/
theorem logActiveKernel_diagonal (a : ι → ℕ) (S : Finset ℕ) (i : ι)
    (ha : 0 < a i) : logActiveKernel a S i i = 0 := by
  classical
  unfold logActiveKernel
  rw [primeBaselineSum_diagonal a S i ha]
  simp only [outsidePrimeDiagonal, diagonalKernel, if_true]
  have hlog := sum_factorization_log_add_outside S (2 * a i)
  have hcast : ((2 * a i : ℕ) : ℝ) = (a i : ℝ) + (a i : ℝ) := by
    push_cast
    ring
  rw [hcast] at hlog
  linarith

theorem primeExcessKernel_diagonal (a : ι → ℕ) (S : Finset ℕ) (i : ι)
    (ha : 0 < a i) : primeExcessKernel a S i i = 0 := by
  unfold primeExcessKernel
  apply Finset.sum_eq_zero
  intro p _
  rw [← two_mul, ← primeBaseline_diagonal a p i ha, sub_self, mul_zero]

/-- At primes, the valuation excess is entrywise nonnegative. -/
theorem primeExcessKernel_nonneg (a : ι → ℕ) (S : Finset ℕ)
    (ha : ∀ i, 0 < a i) (hS : ∀ p ∈ S, p.Prime) (i j : ι) :
    0 ≤ primeExcessKernel a S i j := by
  unfold primeExcessKernel
  apply Finset.sum_nonneg
  intro p hp
  apply mul_nonneg (Real.log_natCast_nonneg p)
  exact sub_nonneg.2 (primeBaseline_le_factorization_add a (hS p hp) i j (ha i) (ha j))

/-- Complete factorization on off-diagonal sums gives the exact kernel
 decomposition on all entries.  The outside term is retained on the diagonal. -/
theorem log_sum_eq_prime_baselines_add_excess_add_outside (a : ι → ℕ) (S : Finset ℕ)
    (hS : ∀ i j, i ≠ j → (a i + a j).primeFactors ⊆ S) (i j : ι) :
    Real.log ((a i : ℝ) + (a j : ℝ)) =
      primeBaselineSum a S i j + primeExcessKernel a S i j +
        outsidePrimeDiagonal a S i j := by
  classical
  have hsum : primeBaselineSum a S i j + primeExcessKernel a S i j =
      ∑ p ∈ S, ((a i + a j).factorization p : ℝ) * Real.log (p : ℝ) := by
    unfold primeBaselineSum primeExcessKernel
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p _
    ring
  rw [hsum]
  by_cases hij : i = j
  · subst j
    simpa only [outsidePrimeDiagonal, diagonalKernel, if_true, two_mul, Nat.cast_add] using
      (sum_factorization_log_add_outside S (2 * a i)).symm
  · simp only [outsidePrimeDiagonal, diagonalKernel, hij, if_false, add_zero]
    rw [← Nat.cast_add]
    exact (sum_factorization_log_eq_log_of_subset (a i + a j) S (hS i j hij)).symm

/-- The analytic and the finite valuation-excess definitions agree when
 `S` contains the prime factors of all off-diagonal sums. -/
theorem logActiveKernel_eq_primeExcessKernel (a : ι → ℕ) (S : Finset ℕ)
    (hS : ∀ i j, i ≠ j → (a i + a j).primeFactors ⊆ S) (i j : ι) :
    logActiveKernel a S i j = primeExcessKernel a S i j := by
  unfold logActiveKernel
  rw [log_sum_eq_prime_baselines_add_excess_add_outside a S hS i j]
  ring

section ConditionalNegative

variable [Fintype ι]

/-- A diagonal kernel has an explicit weighted sum-of-squares quadratic form. -/
theorem diagonalKernel_qform (d x : ι → ℝ) :
    Paired.qform (diagonalKernel d) x = ∑ i, d i * (x i) ^ 2 := by
  classical
  simp only [Paired.qform, diagonalKernel, mul_ite, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem diagonalKernel_psd (d : ι → ℝ) (hd : ∀ i, 0 ≤ d i) :
    Paired.PSD (diagonalKernel d) := by
  intro x
  rw [diagonalKernel_qform]
  exact Finset.sum_nonneg fun i _ => mul_nonneg (hd i) (sq_nonneg _)

theorem outsidePrimeDiagonal_psd (a : ι → ℕ) (S : Finset ℕ) :
    Paired.PSD (outsidePrimeDiagonal a S) :=
  diagonalKernel_psd _ (fun i => outsidePrimeLog_nonneg S (2 * a i))

/-- Subtracting a PSD kernel preserves conditional negative semidefiniteness
 of the positive-real logarithmic sum kernel. -/
theorem log_sum_sub_psd_cnd (a : ι → ℝ) (ha : ∀ i, 0 < a i)
    (P : ι → ι → ℝ) (hP : Paired.PSD P) :
    Paired.CND (fun i j => Real.log (a i + a j) - P i j) := by
  intro x hx
  have hlog := log_sum_cnd a x ha hx
  have hnonneg := hP x
  simp only [Paired.qform, mul_sub, Finset.sum_sub_distrib]
  change Paired.qform (fun i j => Real.log (a i + a j)) x - Paired.qform P x ≤ 0
  exact sub_nonpos.2 (le_trans hlog hnonneg)

/-- Any nonnegative outside-support diagonal can be removed together with
 the prime baselines without losing CND. -/
theorem log_sum_sub_prime_baselines_cnd (a : ι → ℕ) (ha : ∀ i, 0 < a i)
    (S : Finset ℕ) (d : ι → ℝ) (hd : ∀ i, 0 ≤ d i) :
    Paired.CND (fun i j => Real.log ((a i : ℝ) + (a j : ℝ)) -
      primeBaselineSum a S i j - diagonalKernel d i j) := by
  have hP : Paired.PSD (fun i j => primeBaselineSum a S i j + diagonalKernel d i j) := by
    intro x
    simp only [Paired.qform, mul_add, Finset.sum_add_distrib]
    exact add_nonneg (primeBaselineSum_psd a S x) (diagonalKernel_psd d hd x)
  have haR : ∀ i, 0 < (a i : ℝ) := fun i => Nat.cast_pos.2 (ha i)
  simpa only [sub_add_eq_sub_sub] using
    log_sum_sub_psd_cnd (fun i => (a i : ℝ)) haR _ hP

/-- Reusable decomposition form: an active kernel is CND if logsum is
 its sum with the prime baselines and a nonnegative diagonal. -/
theorem cnd_of_log_sum_baseline_decomposition (a : ι → ℕ) (ha : ∀ i, 0 < a i)
    (S : Finset ℕ) (d : ι → ℝ) (hd : ∀ i, 0 ≤ d i) (L : ι → ι → ℝ)
    (hL : ∀ i j, Real.log ((a i : ℝ) + (a j : ℝ)) =
      L i j + primeBaselineSum a S i j + diagonalKernel d i j) :
    Paired.CND L := by
  have he : L = (fun i j => Real.log ((a i : ℝ) + (a j : ℝ)) -
      primeBaselineSum a S i j - diagonalKernel d i j) := by
    funext i j
    linarith [hL i j]
  rw [he]
  exact log_sum_sub_prime_baselines_cnd a ha S d hd

/-- The zero-diagonal logarithmic active kernel is CND for every finite
 set `S`.  Completeness of `S` is needed only to identify it with the
 finite sum of valuation excess. -/
theorem logActiveKernel_cnd (a : ι → ℕ) (ha : ∀ i, 0 < a i) (S : Finset ℕ) :
    Paired.CND (logActiveKernel a S) := by
  unfold logActiveKernel outsidePrimeDiagonal
  exact log_sum_sub_prime_baselines_cnd a ha S _
    (fun i => outsidePrimeLog_nonneg S (2 * a i))

/-- The finite sum of prime valuation excess is a zero-diagonal CND
 kernel when `S` contains every prime factor of every off-diagonal sum. -/
theorem primeExcessKernel_cnd (a : ι → ℕ) (ha : ∀ i, 0 < a i) (S : Finset ℕ)
    (hS : ∀ i j, i ≠ j → (a i + a j).primeFactors ⊆ S) :
    Paired.CND (primeExcessKernel a S) := by
  have he : logActiveKernel a S = primeExcessKernel a S :=
    funext fun i => funext fun j => logActiveKernel_eq_primeExcessKernel a S hS i j
  rw [← he]
  exact logActiveKernel_cnd a ha S

end ConditionalNegative

end Erdos126Aux
