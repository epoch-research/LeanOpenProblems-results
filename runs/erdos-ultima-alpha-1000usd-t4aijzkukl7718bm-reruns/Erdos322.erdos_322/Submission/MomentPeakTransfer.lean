import Submission.MomentReduction

/-!
A near-linear moment criterion for the full representation count.
This supplies a sufficient route to power peaks, not the required moment lower bound.
-/
namespace Erdos322.MomentReduction

noncomputable section

/-- Every fixed moment has an arbitrarily small loss over linear growth. -/
def NearLinearMoments (r : ℕ → ℕ) : Prop :=
  ∀ q : ℕ, 1 ≤ q → ∀ ε > (0 : ℝ), ∃ C > (0 : ℝ),
    ∀ N : ℕ, 1 ≤ N → countMoment r q N ≤ C * (N : ℝ)^(1+ε)

/-- A pointwise bound controls a moment in terms of the first moment. -/
theorem countMoment_le_bound_mul_first (r : ℕ → ℕ) (q N : ℕ)
    (hq : 1 ≤ q) (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ n ∈ Finset.Icc 1 N, (r n : ℝ) ≤ B) :
    countMoment r q N ≤ B^q * countMoment r 1 N := by
  calc
    countMoment r q N ≤ ∑ n ∈ Finset.Icc 1 N, B^q * (r n : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      by_cases hz : r n = 0
      · simp [hz, Nat.ne_of_gt (show 0 < q by omega)]
      · have hr : (1 : ℝ) ≤ r n := by
          exact_mod_cast Nat.one_le_iff_ne_zero.mpr hz
        calc
          (r n : ℝ)^q ≤ B^q := pow_le_pow_left₀ (by positivity) (hb n hn) q
          _ = B^q * 1 := (mul_one _).symm
          _ ≤ B^q * (r n : ℝ) := mul_le_mul_of_nonneg_left hr (pow_nonneg hB q)
    _ = B^q * countMoment r 1 N := by simp [countMoment, Finset.mul_sum]

/-- With a linear first moment, subpolynomial pointwise bounds are equivalent
 to near-linear bounds for every fixed moment. -/
theorem subpolynomial_iff_near_linear_moments (r : ℕ → ℕ)
    (A : ℝ) (hA : 0 < A)
    (hfirst : ∀ N : ℕ, 1 ≤ N → countMoment r 1 N ≤ A*(N : ℝ)) :
    Subpolynomial r ↔ NearLinearMoments r := by
  constructor
  · intro hs q hq ε hε
    have hqr : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
    obtain ⟨B, hB, hb⟩ := hs (ε/(q : ℝ)) (by positivity)
    refine ⟨A*B^q, mul_pos hA (pow_pos hB q), ?_⟩
    intro N hN
    have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hbound : ∀ n ∈ Finset.Icc 1 N,
        (r n : ℝ) ≤ B*(N : ℝ)^(ε/(q : ℝ)) := by
      intro n hn
      obtain ⟨hn1, hnN⟩ := Finset.mem_Icc.mp hn
      exact (hb n hn1).trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hnN)
          (by positivity)) hB.le)
    have hp : ((N : ℝ)^(ε/(q : ℝ)))^q = (N : ℝ)^ε := by
      rw [← Real.rpow_mul_natCast hNr.le, div_mul_cancel₀ _ hqr.ne']
    calc
      countMoment r q N ≤ (B*(N : ℝ)^(ε/(q : ℝ)))^q * countMoment r 1 N :=
        countMoment_le_bound_mul_first r q N hq _ (by positivity) hbound
      _ ≤ (B*(N : ℝ)^(ε/(q : ℝ)))^q * (A*(N : ℝ)) :=
        mul_le_mul_of_nonneg_left (hfirst N hN) (by positivity)
      _ = (A*B^q) * (N : ℝ)^(1+ε) := by
        rw [mul_pow, hp, Real.rpow_add hNr, Real.rpow_one]
        ring
  · intro hm
    apply (subpolynomial_iff_quadratic_moments r).mpr
    intro q hq
    obtain ⟨C, hC, hb⟩ := hm q hq 1 (by norm_num)
    refine ⟨C, hC, ?_⟩
    intro N hN
    simpa only [show (1:ℝ)+1=2 by norm_num, Real.rpow_two] using hb N hN

/-- The criterion applies to the full count for every positive exponent. -/
theorem representation_subpolynomial_iff_near_linear (k : ℕ) (hk : 0 < k) :
    Subpolynomial (representationCount k) ↔
      NearLinearMoments (representationCount k) := by
  exact subpolynomial_iff_near_linear_moments _ ((2:ℝ)^k) (by positivity)
    (fun N hN => first_moment_linear k N hk hN)

/-- A single fixed moment failing some superlinear power bound is enough to
 force positive-power peaks. Conversely, power peaks force such a failure. -/
theorem polynomial_peaks_iff_moment_failure (k : ℕ) (hk : 0 < k) :
    (∃ c > (0 : ℝ),
      {n : ℕ | (n : ℝ)^c < representationCount k n}.Infinite) ↔
    ∃ q : ℕ, 1 ≤ q ∧ ∃ ε > (0 : ℝ),
      ¬ (∃ C > (0 : ℝ), ∀ N : ℕ, 1 ≤ N →
        countMoment (representationCount k) q N ≤ C*(N : ℝ)^(1+ε)) := by
  classical
  have he := (Erdos322Research.no_polynomial_peaks_iff_uniform_bound
    (representationCount k)).trans (representation_subpolynomial_iff_near_linear k hk)
  constructor
  · intro hp
    by_contra hn
    apply (he.mpr ?_) hp
    push_neg at hn
    exact hn
  · rintro ⟨q, hq, ε, hε, hm⟩
    by_contra hp
    exact hm ((he.mp hp) q hq ε hε)

/-- A concrete check of the stronger moment criterion: the thirteenth cubic
moment is not bounded by a constant times `N^(13/12)`. -/
theorem cubic_thirteenth_moment_not_thirteen_twelfths :
    ¬ (∃ C > (0 : ℝ), ∀ N : ℕ, 1 ≤ N →
      countMoment (representationCount 3) 13 N ≤
        C*(N : ℝ)^(1+(1/12 : ℝ))) := by
  rintro ⟨C, hC, hbound⟩
  obtain ⟨m, hm⟩ := exists_nat_gt (max 1 (C*2^13))
  have hmpos : 0 < m := by
    have hmr : (0 : ℝ) < m := lt_of_lt_of_le zero_lt_one
      ((le_max_left _ _).trans hm.le)
    exact_mod_cast hmr
  have hCm : C*2^13 < (m : ℝ) := (le_max_right _ _).trans_lt hm
  have hn : 1 ≤ (6*m)^12 := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hlow := cubic_moment_block_lower 13 m hmpos
  have hup := hbound ((6*m)^12) hn
  have hnorm : (((6*m)^12 : ℕ) : ℝ)^(1+(1/12 : ℝ)) = (6*(m : ℝ))^13 := by
    rw [Nat.cast_pow, Nat.cast_mul, Nat.cast_ofNat,
      ← Real.rpow_natCast (6*(m : ℝ)) 12, ← Real.rpow_mul (by positivity)]
    norm_num
  rw [hnorm] at hup
  have hstrict : C*(6*(m : ℝ))^13 < (m : ℝ)*(3*(m : ℝ))^13 := by
    calc
      C*(6*(m : ℝ))^13 = (C*2^13)*(3*(m : ℝ))^13 := by ring
      _ < (m : ℝ)*(3*(m : ℝ))^13 :=
        mul_lt_mul_of_pos_right hCm (by positivity)
  exact not_lt_of_ge (hlow.trans hup) hstrict

/-- Recover the cubic peak statement using only the moment-transfer route. -/
theorem cubic_peaks_from_thirteenth_moment :
    ∃ c > (0 : ℝ),
      {n : ℕ | (n : ℝ)^c < representationCount 3 n}.Infinite := by
  apply (polynomial_peaks_iff_moment_failure 3 (by decide)).mpr
  exact ⟨13, by decide, 1/12, by norm_num,
    cubic_thirteenth_moment_not_thirteen_twelfths⟩

end

end Erdos322.MomentReduction
