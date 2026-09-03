import Submission.HardCubicTransfer
import Submission.SelbergNormalizerAdditive
import Submission.SelbergCubicEnergy

/-! Prime-indexed hard-cubic norm, coordinate energy, and coefficient cost.
These estimates do not yet assert a Jacobsthal power bound. -/
namespace Erdos970.FiniteSelberg
open Finset Real
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
set_option maxHeartbeats 1000000

noncomputable def primeHardCubicProfile (p : ι → ℕ) (L : ℝ) (Q : Finset ι) : ℝ :=
  hardCubicProfile L (primeLogLocation p Q)

lemma hardCubicProfile_zero (L x : ℝ) (hx : L ≤ x) : hardCubicProfile L x = 0 := by
  simp only [hardCubicProfile, cutoffValue, if_neg (not_lt.mpr hx)]

lemma hardCubicProfile_shift_cap (L a v : ℝ) (ha : 0 ≤ a) :
    hardCubicProfile L (a + v) = hardCubicProfile L (a + min v L) := by
  by_cases hv : v ≤ L
  · rw [min_eq_left hv]
  · rw [min_eq_right (le_of_not_ge hv),
      hardCubicProfile_zero L (a + v) (by linarith),
      hardCubicProfile_zero L (a + L) (by linarith)]

lemma primeHardCubicProfile_difference (p : ι → ℕ) (L : ℝ)
    (Q : Finset ι) (i : ι) (hi : i ∉ Q) :
    primeHardCubicProfile p L Q - primeHardCubicProfile p L (insert i Q) =
      hardCubicProfile L (primeLogLocation p Q) -
        hardCubicProfile L (primeLogLocation p Q + min (log (p i : ℝ)) L) := by
  unfold primeHardCubicProfile
  have he : primeLogLocation p (insert i Q) = primeLogLocation p Q + log (p i : ℝ) := by
    unfold primeLogLocation
    rw [sum_insert hi, add_comm]
  rw [he, hardCubicProfile_shift_cap L _ _ (primeLogLocation_nonneg p Q)]

theorem prime_hardCubic_square_error (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (hinj : Function.Injective p) (R : ℕ) (hR : 0 < R)
    (hfull : ∀ a, a.Prime → a ≤ R → ∃ i, p i = a) :
    |(∑ Q : Finset ι, weight (fun i => 1 / (p i : ℝ)) Q * primeHardCubicProfile p (log R) Q ^ 2) -
      hardCubicNorm * log (R : ℝ) ^ 7| ≤
      800000000 * additiveNormalizerConstant * log (R : ℝ) ^ 6 :=
  hardCubic_square_error (weight (fun i => 1 / (p i : ℝ))) (primeLogLocation p)
    (primeLogLocation_nonneg p) (log R) additiveNormalizerConstant (log_natCast_nonneg R)
    additiveNormalizerConstant_pos.le
    (fun t ht => cumulative_prime_error_additive p hp hinj R hR hfull t ht.1 ht.2)

lemma prime_hardCubic_dirichlet_coordinate (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (hinj : Function.Injective p) (R : ℕ) (hR : 0 < R)
    (hfull : ∀ a, a.Prime → a ≤ R → ∃ i, p i = a) (i : ι) :
    (∑ Q ∈ (univ.erase i).powerset, weight (fun i => 1 / (p i : ℝ)) Q *
      (primeHardCubicProfile p (log R) Q - primeHardCubicProfile p (log R) (insert i Q)) ^ 2) ≤
      hardCubicShiftMain (log R) (min (log (p i : ℝ)) (log R)) +
        3200000000 * additiveNormalizerConstant * log (R : ℝ) ^ 6 := by
  let L := log (R : ℝ)
  let v := min (log (p i : ℝ)) L
  have hL : 0 ≤ L := log_natCast_nonneg R
  have hv : 0 ≤ v := le_min (log_natCast_nonneg _) hL
  have hvL : v ≤ L := min_le_right _ _
  have hh := hardCubic_difference_error (weight (fun i => 1 / (p i : ℝ)))
    (primeLogLocation p) (primeLogLocation_nonneg p) L v additiveNormalizerConstant hv hvL
    additiveNormalizerConstant_pos.le
    (fun t ht => cumulative_prime_error_additive p hp hinj R hR hfull t ht.1 ht.2)
  have hup := (abs_le.mp hh).2
  have hs : (∑ Q ∈ (univ.erase i).powerset, weight (fun i => 1 / (p i : ℝ)) Q *
      (primeHardCubicProfile p L Q - primeHardCubicProfile p L (insert i Q)) ^ 2) ≤
      ∑ Q : Finset ι, weight (fun i => 1 / (p i : ℝ)) Q *
        (hardCubicProfile L (primeLogLocation p Q) - hardCubicProfile L (primeLogLocation p Q + v)) ^ 2 := by
    calc
      _ = ∑ Q ∈ (univ.erase i).powerset, weight (fun i => 1 / (p i : ℝ)) Q *
          (hardCubicProfile L (primeLogLocation p Q) - hardCubicProfile L (primeLogLocation p Q + v)) ^ 2 := by
        apply sum_congr rfl
        intro Q hQ
        rw [primeHardCubicProfile_difference p L Q i (not_mem_of_erase_powerset hQ)]
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg (subset_univ _)
        (fun Q _ _ => mul_nonneg (weight_pos _ (prime_marginals p hp) Q).le (sq_nonneg _))
  change _ ≤ hardCubicShiftMain L v + 3200000000 * additiveNormalizerConstant * L ^ 6
  linarith

/-- The reciprocal-prime factor in the accumulated discontinuity error is
  explicit. It cannot be replaced by a constant without a further estimate. -/
theorem prime_hardCubic_dirichlet_le (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (hinj : Function.Injective p) (R : ℕ) (hR : 0 < R)
    (hfull : ∀ a, a.Prime → a ≤ R → ∃ i, p i = a) :
    (∑ i, (1 / (p i : ℝ)) * ∑ Q ∈ (univ.erase i).powerset,
      weight (fun i => 1 / (p i : ℝ)) Q *
        (primeHardCubicProfile p (log R) Q - primeHardCubicProfile p (log R) (insert i Q)) ^ 2) ≤
      (∑ i, (1 / (p i : ℝ)) * hardCubicShiftMain (log R) (min (log (p i : ℝ)) (log R))) +
      3200000000 * additiveNormalizerConstant * log (R : ℝ) ^ 6 * ∑ i, 1 / (p i : ℝ) := by
  calc
    _ ≤ ∑ i, (1 / (p i : ℝ)) *
        (hardCubicShiftMain (log R) (min (log (p i : ℝ)) (log R)) +
          3200000000 * additiveNormalizerConstant * log (R : ℝ) ^ 6) :=
      sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left
        (prime_hardCubic_dirichlet_coordinate p hp hinj R hR hfull i) (by positivity))
    _ = _ := by simp only [mul_add, sum_add_distrib, mul_sum]; congr 1; apply sum_congr rfl; intros; ring

lemma prime_hardCubic_support (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (R : ℕ) (hR : 0 < R) (Q : Finset ι) (hQ : Q ∉ divisorSupport p R) :
    primeHardCubicProfile p (log R) Q = 0 := by
  have hRQ : R < ∏ i ∈ Q, p i := by simpa only [mem_divisorSupport, not_le] using hQ
  apply hardCubicProfile_zero
  rw [primeLogLocation_eq_log_prod p hp]
  exact log_le_log (by exact_mod_cast hR) (by exact_mod_cast hRQ.le)

lemma prime_hardCubic_cost_le (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (hinj : Function.Injective p) (R : ℕ) (hR : 0 < R) :
    kernelCost (fun i => 1 / (p i : ℝ))
      (fun Q => weight (fun i => 1 / (p i : ℝ)) Q * primeHardCubicProfile p (log R) Q) ≤
        10000 * log (R : ℝ) ^ 3 * exp 2 * R := by
  let f := primeHardCubicProfile p (log R)
  let D := divisorSupport p R
  have hb (Q : Finset ι) : 0 ≤ f Q ∧ f Q ≤ 10000 * log (R : ℝ) ^ 3 :=
    hardCubicProfile_bounds (log R) (primeLogLocation p Q) (log_natCast_nonneg R)
      (primeLogLocation_nonneg p Q)
  have hpred (i : ι) : 0 < (p i : ℝ) - 1 := by
    have hh : (1 : ℝ) < p i := by exact_mod_cast (hp i).one_lt
    linarith
  have hfactor (i : ι) : (1 + 1 / (p i : ℝ)) / (1 - 1 / (p i : ℝ)) =
      ((p i : ℝ) + 1) / (p i - 1) := by
    have hpi : (p i : ℝ) ≠ 0 := by exact_mod_cast (hp i).ne_zero
    field_simp [hpi, (hpred i).ne']
    <;> ring
  rw [kernelCost_weighted _ (prime_marginals p hp) _ (fun Q => (hb Q).1)]
  simp_rw [hfactor]
  calc
    _ = ∑ Q ∈ D, f Q * ∏ i ∈ Q, ((p i : ℝ) + 1) / (p i - 1) := by
      symm
      apply sum_subset (subset_univ _)
      intro Q hQ hQD
      rw [show f Q = 0 from prime_hardCubic_support p hp R hR Q hQD, zero_mul]
    _ ≤ (10000 * log (R : ℝ) ^ 3) * ∑ Q ∈ D, ∏ i ∈ Q, ((p i : ℝ) + 1) / (p i - 1) := by
      rw [mul_sum]
      apply sum_le_sum
      intro Q hQ
      apply mul_le_mul_of_nonneg_right (hb Q).2
      exact prod_nonneg (fun i _ => div_nonneg (by positivity) (hpred i).le)
    _ ≤ (10000 * log (R : ℝ) ^ 3) * (exp 2 * R) :=
      mul_le_mul_of_nonneg_left (divisor_cost_sum_le p hp hinj R)
        (by have := log_natCast_nonneg R; positivity)
    _ = _ := by ring

#print axioms prime_hardCubic_square_error
#print axioms prime_hardCubic_dirichlet_le
#print axioms prime_hardCubic_cost_le
end Erdos970.FiniteSelberg
