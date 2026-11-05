import Submission.Comparison

/-!
# Exact dyadic flux and a conditional finite-scale Tauberian helper

This file contains helper formalizations, not a proof of Erdős Problem 371.
It does not import `Submission.Spec` or assume any logarithmic-density theorem.

The sum `comparisonSum N` has the inclusive interval `[2, N]`. Its signed
nonmedian part uses exactly the strict-between predicate of `comparisonSum_odd`.
For positive `N`, the dyadic increment of `comparisonSum N / N` is the negative
normalized nonmedian sum minus the boundary sign `s(2*N+1)/(2*N)`.

The generic Tauberian theorem has two explicit hypotheses: vanishing all-scale
dyadic increments, and a finite dyadic recurrence property. The latter is NOT
proved for the prime-factor comparison sequence here. In particular, neither
all-scale nonmedian cancellation nor the original density limit is established.
-/

open Filter
open scoped Topology

namespace DyadicTauberian

/-- The all-scale dyadic increment of a real sequence. -/
def dyadicIncrement (A : ℕ → ℝ) (N : ℕ) : ℝ := A (2 * N) - A N

/-- For every positive tolerance, a bounded number of dyadic dilations contains
one small sample, uniformly for all sufficiently large starting scales.
This is an explicit hypothesis, not a density-theoretic conclusion. -/
def FiniteDyadicRecurrence (A : ℕ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ J : ℕ,
    ∀ᶠ N : ℕ in atTop, ∃ j : ℕ, j ≤ J ∧ |A (2 ^ j * N)| < ε

/-- Every fixed dyadic dilation of the natural scale tends to infinity. -/
theorem tendsto_dyadic_dilate_atTop (j : ℕ) :
    Tendsto (fun N : ℕ => 2 ^ j * N) atTop atTop :=
  tendsto_atTop_mono (fun N => Nat.le_mul_of_pos_left N (by positivity)) tendsto_id

/-- Exact finite telescope along a dyadic orbit, including zero steps and scale zero. -/
theorem dyadic_telescope (A : ℕ → ℝ) (N j : ℕ) :
    A (2 ^ j * N) - A N =
      ∑ i ∈ Finset.range j, dyadicIncrement A (2 ^ i * N) := by
  simpa [dyadicIncrement, pow_succ, mul_assoc, mul_left_comm, mul_comm] using
    (Finset.sum_range_sub (fun i => A (2 ^ i * N)) j).symm

/-- A uniform increment bound on a finite orbit bounds its total displacement. -/
theorem abs_dyadic_difference_le (A : ℕ → ℝ) (N j : ℕ) (δ : ℝ)
    (hδ : ∀ i < j, |dyadicIncrement A (2 ^ i * N)| ≤ δ) :
    |A (2 ^ j * N) - A N| ≤ (j : ℝ) * δ := by
  rw [dyadic_telescope]
  calc
    _ ≤ ∑ i ∈ Finset.range j, |dyadicIncrement A (2 ^ i * N)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ Finset.range j, δ :=
      Finset.sum_le_sum fun i hi => hδ i (Finset.mem_range.mp hi)
    _ = (j : ℝ) * δ := by simp

/-- Quantitative finite Tauberian bound: transport a small sample back to the
starting scale, paying at most one increment bound per step. -/
theorem abs_le_sample_add (A : ℕ → ℝ) (N j : ℕ) (δ : ℝ)
    (hδ : ∀ i < j, |dyadicIncrement A (2 ^ i * N)| ≤ δ) :
    |A N| ≤ |A (2 ^ j * N)| + (j : ℝ) * δ := by
  calc
    |A N| = |A (2 ^ j * N) + (A N - A (2 ^ j * N))| := by
      congr 1
      ring
    _ ≤ |A (2 ^ j * N)| + |A N - A (2 ^ j * N)| := abs_add_le _ _
    _ = |A (2 ^ j * N)| + |A (2 ^ j * N) - A N| := by rw [abs_sub_comm]
    _ ≤ _ := add_le_add (le_refl _) (abs_dyadic_difference_le A N j δ hδ)

/-- Vanishing increments give vanishing displacement at any fixed dyadic dilation. -/
theorem tendsto_dyadic_difference_zero {A : ℕ → ℝ}
    (hinc : Tendsto (dyadicIncrement A) atTop (𝓝 0)) (j : ℕ) :
    Tendsto (fun N : ℕ => A (2 ^ j * N) - A N) atTop (𝓝 0) := by
  have hsum := tendsto_finset_sum (Finset.range j)
    (fun i _ => hinc.comp (tendsto_dyadic_dilate_atTop i))
  simpa only [Function.comp_def, Finset.sum_const_zero, ← dyadic_telescope A] using hsum

/-- Fixed finite sets of dyadic displacements tend to zero uniformly. The bound
`J` is fixed before taking the scale limit. -/
theorem finite_uniform_dyadic_differences {A : ℕ → ℝ}
    (hinc : Tendsto (dyadicIncrement A) atTop (𝓝 0)) (J : ℕ)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ j : ℕ, j ≤ J → |A (2 ^ j * N) - A N| < ε := by
  have hfinite : ∀ᶠ N : ℕ in atTop,
      ∀ j ∈ Finset.range (J + 1), |A (2 ^ j * N) - A N| < ε := by
    apply (eventually_all_finset (Finset.range (J + 1))).mpr
    intro j _
    simpa only [abs_zero] using
      (tendsto_order.mp (tendsto_dyadic_difference_zero hinc j).abs).2 ε
        (by simpa only [abs_zero] using hε)
  simpa only [Finset.mem_range, Nat.lt_succ_iff] using hfinite

/-- Generic finite-scale Tauberian rigidity. Both hypotheses are visible; no
boundedness of `A` and no unformalized density theorem are needed. -/
theorem tendsto_zero_of_finiteDyadicRecurrence {A : ℕ → ℝ}
    (hrec : FiniteDyadicRecurrence A)
    (hinc : Tendsto (dyadicIncrement A) atTop (𝓝 0)) :
    Tendsto A atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨J, hJ⟩ := hrec (ε / 2) (half_pos hε)
  filter_upwards [hJ, finite_uniform_dyadic_differences hinc J (half_pos hε)]
    with N hsmall hdiff
  obtain ⟨j, hj, hsample⟩ := hsmall
  have htri := abs_sub_le (A N) (A (2 ^ j * N)) 0
  rw [sub_zero, sub_zero, abs_sub_comm (A N) (A (2 ^ j * N))] at htri
  have hbound := hdiff j hj
  have hlt : |A N| < ε := by linarith
  simpa only [Real.dist_eq, sub_zero] using hlt

/-- A zero limit always implies vanishing all-scale dyadic increments. -/
theorem dyadicIncrement_tendsto_zero_of_tendsto_zero {A : ℕ → ℝ}
    (hA : Tendsto A atTop (𝓝 0)) :
    Tendsto (dyadicIncrement A) atTop (𝓝 0) := by
  simpa only [dyadicIncrement, pow_one, sub_zero] using
    (hA.comp (tendsto_dyadic_dilate_atTop 1)).sub hA

/-- Under the explicit recurrence hypothesis, zero limit and dyadic regularity
are equivalent. This theorem does not discharge that hypothesis. -/
theorem tendsto_zero_iff_dyadicIncrement {A : ℕ → ℝ}
    (hrec : FiniteDyadicRecurrence A) :
    Tendsto A atTop (𝓝 0) ↔ Tendsto (dyadicIncrement A) atTop (𝓝 0) :=
  ⟨dyadicIncrement_tendsto_zero_of_tendsto_zero,
    tendsto_zero_of_finiteDyadicRecurrence hrec⟩

end DyadicTauberian

namespace Erdos371

/-- Signed nonmedian sum on the inclusive interval `[2,N]`. The predicate here
is literally the strict-between predicate in `comparisonSum_odd`, not an
approximate median, a non-strict comparison, or an unsigned exceptional count. -/
def nonmedianSum (N : ℕ) : ℤ :=
  ∑ m ∈ Finset.Icc 2 N,
    if min (Nat.maxPrimeFac m) (Nat.maxPrimeFac (m + 1)) <
          Nat.maxPrimeFac (2 * m + 1) ∧
        Nat.maxPrimeFac (2 * m + 1) <
          max (Nat.maxPrimeFac m) (Nat.maxPrimeFac (m + 1)) then
      0
    else comparisonSign m

@[simp]
theorem nonmedianSum_zero : nonmedianSum 0 = 0 := by simp [nonmedianSum]

@[simp]
theorem nonmedianSum_one : nonmedianSum 1 = 0 := by simp [nonmedianSum]

/-- Exact signed flux form of the odd-endpoint identity, valid for ALL `N`,
including `0` and `1`, where both parent intervals are empty. -/
theorem comparisonSum_odd_eq_two_mul_sub_nonmedianSum (N : ℕ) :
    comparisonSum (2 * N + 1) = 2 * (comparisonSum N - nonmedianSum N) := by
  rw [comparisonSum_odd, comparisonSum, nonmedianSum, ← Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro m _
  split_ifs <;> simp

/-- Removing the final odd boundary sign. Positivity is essential for this
unnormalized identity: it is false at `N = 0`. -/
theorem comparisonSum_double_eq_two_mul_sub_nonmedianSum {N : ℕ} (hN : 0 < N) :
    comparisonSum (2 * N) =
      2 * (comparisonSum N - nonmedianSum N) - comparisonSign (2 * N + 1) := by
  have htop : comparisonSum (2 * N + 1) =
      comparisonSum (2 * N) + comparisonSign (2 * N + 1) :=
    Finset.sum_Icc_succ_top (by omega) comparisonSign
  rw [comparisonSum_odd_eq_two_mul_sub_nonmedianSum] at htop
  omega

/-- Inclusive signed bias; real division is total, so its value at zero is zero. -/
noncomputable def normalizedComparisonSum (N : ℕ) : ℝ := (comparisonSum N : ℝ) / N

/-- The signed nonmedian flux `Φ(N)`, not the proportion of nonmedian parents. -/
noncomputable def normalizedNonmedianFlux (N : ℕ) : ℝ := (nonmedianSum N : ℝ) / N

/-- The exact single-sign error at the odd endpoint. -/
noncomputable def dyadicBoundary (N : ℕ) : ℝ :=
  (comparisonSign (2 * N + 1) : ℝ) / (2 * (N : ℝ))

@[simp]
theorem normalizedComparisonSum_zero : normalizedComparisonSum 0 = 0 := by
  simp [normalizedComparisonSum]

@[simp]
theorem normalizedComparisonSum_one : normalizedComparisonSum 1 = 0 := by
  simp [normalizedComparisonSum, comparisonSum]

@[simp]
theorem normalizedNonmedianFlux_zero : normalizedNonmedianFlux 0 = 0 := by
  simp [normalizedNonmedianFlux]

@[simp]
theorem normalizedNonmedianFlux_one : normalizedNonmedianFlux 1 = 0 := by
  simp [normalizedNonmedianFlux]

@[simp]
theorem dyadicBoundary_zero : dyadicBoundary 0 = 0 := by simp [dyadicBoundary]

/-- Exact normalized formula with the correct boundary `s(2*N+1)`, for `N > 0`. -/
theorem normalizedComparisonSum_double {N : ℕ} (hN : 0 < N) :
    normalizedComparisonSum (2 * N) =
      normalizedComparisonSum N - normalizedNonmedianFlux N - dyadicBoundary N := by
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)
  unfold normalizedComparisonSum normalizedNonmedianFlux dyadicBoundary
  rw [comparisonSum_double_eq_two_mul_sub_nonmedianSum hN]
  push_cast
  field_simp

/-- The dyadic increment identity is also valid at zero, by total real division.
This does not extend the false unnormalized even-endpoint identity to zero. -/
theorem dyadicIncrement_normalizedComparisonSum (N : ℕ) :
    DyadicTauberian.dyadicIncrement normalizedComparisonSum N =
      -normalizedNonmedianFlux N - dyadicBoundary N := by
  by_cases hN : N = 0
  · subst N
    simp [DyadicTauberian.dyadicIncrement]
  · unfold DyadicTauberian.dyadicIncrement
    rw [normalizedComparisonSum_double (Nat.pos_of_ne_zero hN)]
    ring

/-- Exact boundary size, including zero under the total-division convention. -/
theorem abs_dyadicBoundary (N : ℕ) :
    |dyadicBoundary N| = 1 / (2 * (N : ℝ)) := by
  rcases comparisonSign_eq_one_or_neg_one (2 * N + 1) with h | h <;>
    simp [dyadicBoundary, h, abs_div, abs_mul,
      abs_of_nonneg (show (0 : ℝ) ≤ (N : ℝ) from Nat.cast_nonneg N)]

/-- The boundary term tends to zero on ALL scales, using only boundedness of a sign. -/
theorem dyadicBoundary_tendsto_zero : Tendsto dyadicBoundary atTop (𝓝 0) := by
  unfold dyadicBoundary
  apply tendsto_bdd_div_atTop_nhds_zero (b := (-1 : ℝ)) (B := (1 : ℝ))
  · exact Eventually.of_forall fun N => by
      rcases comparisonSign_eq_one_or_neg_one (2 * N + 1) with h | h <;>
        rw [h] <;> norm_num
  · exact Eventually.of_forall fun N => by
      rcases comparisonSign_eq_one_or_neg_one (2 * N + 1) with h | h <;>
        rw [h] <;> norm_num
  · exact tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num : (0 : ℝ) < 2)

/-- All-scale dyadic regularity is equivalent to all-scale signed nonmedian-flux
cancellation. Neither side of this equivalence is asserted unconditionally. -/
theorem dyadicIncrement_tendsto_zero_iff_normalizedNonmedianFlux :
    Tendsto (DyadicTauberian.dyadicIncrement normalizedComparisonSum) atTop (𝓝 0) ↔
      Tendsto normalizedNonmedianFlux atTop (𝓝 0) := by
  have heq : DyadicTauberian.dyadicIncrement normalizedComparisonSum =
      fun N => -normalizedNonmedianFlux N - dyadicBoundary N :=
    funext dyadicIncrement_normalizedComparisonSum
  rw [heq]
  constructor
  · intro h
    have hneg : Tendsto (fun N => -normalizedNonmedianFlux N) atTop (𝓝 0) := by
      simpa only [sub_add_cancel, add_zero] using h.add dyadicBoundary_tendsto_zero
    simpa only [neg_neg, neg_zero] using hneg.neg
  · intro h
    simpa only [neg_zero, sub_zero] using h.neg.sub dyadicBoundary_tendsto_zero

/-- Conditional prime-factor specialization of finite-scale rigidity. The
recurrence hypothesis remains explicit and is not supplied by this file. -/
theorem normalizedComparisonSum_tendsto_zero_iff_normalizedNonmedianFlux
    (hrec : DyadicTauberian.FiniteDyadicRecurrence normalizedComparisonSum) :
    Tendsto normalizedComparisonSum atTop (𝓝 0) ↔
      Tendsto normalizedNonmedianFlux atTop (𝓝 0) :=
  (DyadicTauberian.tendsto_zero_iff_dyadicIncrement hrec).trans
    dyadicIncrement_tendsto_zero_iff_normalizedNonmedianFlux

/-- Explicit `N = 1` check: `S(1)=Φ(1)=0`, while the boundary is `-1/2` and
`A(2)-A(1)=1/2`. Thus omitting the odd boundary would already fail here. -/
theorem dyadic_flux_endpoint_one :
    normalizedComparisonSum 1 = 0 ∧ normalizedNonmedianFlux 1 = 0 ∧
      dyadicBoundary 1 = -(1 / 2) ∧
      DyadicTauberian.dyadicIncrement normalizedComparisonSum 1 = 1 / 2 := by
  have htwo : comparisonSign 2 = 1 := by
    norm_num [comparisonSign, Nat.prime_two.maxPrimeFac_eq_self,
      Nat.prime_three.maxPrimeFac_eq_self]
  have hthree : comparisonSign 3 = -1 := by
    have h := comparisonSign_start_sum
    rw [htwo] at h
    omega
  have hb : dyadicBoundary 1 = -(1 / 2) := by norm_num [dyadicBoundary, hthree]
  refine ⟨normalizedComparisonSum_one, normalizedNonmedianFlux_one, hb, ?_⟩
  rw [dyadicIncrement_normalizedComparisonSum, normalizedNonmedianFlux_one, hb]
  ring

/-- Explicit `N = 0` check of the normalized identity. All normalized terms
vanish; the odd finite-sum identity has empty parent and child intervals. -/
theorem dyadic_flux_endpoint_zero :
    comparisonSum (2 * 0 + 1) = 2 * (comparisonSum 0 - nonmedianSum 0) ∧
      normalizedComparisonSum 0 = 0 ∧ normalizedNonmedianFlux 0 = 0 ∧
      dyadicBoundary 0 = 0 ∧
      DyadicTauberian.dyadicIncrement normalizedComparisonSum 0 = 0 := by
  refine ⟨comparisonSum_odd_eq_two_mul_sub_nonmedianSum 0,
    normalizedComparisonSum_zero, normalizedNonmedianFlux_zero, dyadicBoundary_zero, ?_⟩
  simp [DyadicTauberian.dyadicIncrement]

end Erdos371

#print axioms DyadicTauberian.dyadicIncrement
#print axioms DyadicTauberian.FiniteDyadicRecurrence
#print axioms DyadicTauberian.tendsto_dyadic_dilate_atTop
#print axioms DyadicTauberian.dyadic_telescope
#print axioms DyadicTauberian.abs_dyadic_difference_le
#print axioms DyadicTauberian.abs_le_sample_add
#print axioms DyadicTauberian.tendsto_dyadic_difference_zero
#print axioms DyadicTauberian.finite_uniform_dyadic_differences
#print axioms DyadicTauberian.tendsto_zero_of_finiteDyadicRecurrence
#print axioms DyadicTauberian.dyadicIncrement_tendsto_zero_of_tendsto_zero
#print axioms DyadicTauberian.tendsto_zero_iff_dyadicIncrement
#print axioms Erdos371.nonmedianSum
#print axioms Erdos371.nonmedianSum_zero
#print axioms Erdos371.nonmedianSum_one
#print axioms Erdos371.comparisonSum_odd_eq_two_mul_sub_nonmedianSum
#print axioms Erdos371.comparisonSum_double_eq_two_mul_sub_nonmedianSum
#print axioms Erdos371.normalizedComparisonSum
#print axioms Erdos371.normalizedNonmedianFlux
#print axioms Erdos371.dyadicBoundary
#print axioms Erdos371.normalizedComparisonSum_zero
#print axioms Erdos371.normalizedComparisonSum_one
#print axioms Erdos371.normalizedNonmedianFlux_zero
#print axioms Erdos371.normalizedNonmedianFlux_one
#print axioms Erdos371.dyadicBoundary_zero
#print axioms Erdos371.normalizedComparisonSum_double
#print axioms Erdos371.dyadicIncrement_normalizedComparisonSum
#print axioms Erdos371.abs_dyadicBoundary
#print axioms Erdos371.dyadicBoundary_tendsto_zero
#print axioms Erdos371.dyadicIncrement_tendsto_zero_iff_normalizedNonmedianFlux
#print axioms Erdos371.normalizedComparisonSum_tendsto_zero_iff_normalizedNonmedianFlux
#print axioms Erdos371.dyadic_flux_endpoint_one
#print axioms Erdos371.dyadic_flux_endpoint_zero
