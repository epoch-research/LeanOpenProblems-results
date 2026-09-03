import Submission.PolylogPowerPrimeDetector

/-! A normalized adaptive Euler product gives a single logarithmic-degree
prime detector. Its composite error is summable, and it equals one at every
prime. No pointwise prime-input divergence is asserted. -/
namespace Erdos972LogDegreePrimeDetector

open Finset Filter
open scoped Topology
open Erdos972NonlinearPrimeProxy Erdos972PolylogMomentPrimeProxy
open Erdos972SmoothMangoldt Erdos972SmoothMangoldtPositive Erdos972PrimePowerError

set_option autoImplicit false
set_option maxHeartbeats 2000000

noncomputable def logParameter (n : ℕ) : ℝ := 2 * Real.log 2 / Real.log n

def logarithmicDegree (n : ℕ) : ℕ := 4 * logSize n

noncomputable def normalizedEuler (n : ℕ) : ℝ :=
  (4 / 3 : ℝ) * expDivisorSum (logParameter n) n

noncomputable def logDetector (n : ℕ) : ℝ :=
  if 1 < n then (normalizedEuler n)^(logarithmicDegree n) else 0

lemma logParameter_nonneg (n : ℕ) : 0 ≤ logParameter n := by
  exact div_nonneg (mul_nonneg (by norm_num) (Real.log_nonneg (by norm_num)))
    (Real.log_natCast_nonneg n)

lemma exp_logParameter {n : ℕ} (hn : 1 < n) :
    Real.exp (-logParameter n * Real.log n) = (1 / 4 : ℝ) := by
  have hnlog : Real.log n ≠ 0 := ne_of_gt (Real.log_pos (by exact_mod_cast hn))
  have he : -logParameter n * Real.log n = -Real.log (4 : ℝ) := by
    unfold logParameter
    have h4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
      simpa only [show (2 : ℝ)^2 = 4 by norm_num, Nat.cast_ofNat] using Real.log_pow (2 : ℝ) 2
    rw [h4]
    field_simp
  rw [he, Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 4)]
  norm_num

lemma exp_half_logParameter {n : ℕ} (hn : 1 < n) :
    Real.exp (-(logParameter n / 2) * Real.log n) = (1 / 2 : ℝ) := by
  have hnlog : Real.log n ≠ 0 := ne_of_gt (Real.log_pos (by exact_mod_cast hn))
  have he : -(logParameter n / 2) * Real.log n = -Real.log (2 : ℝ) := by
    unfold logParameter
    field_simp
  rw [he, Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  norm_num

lemma normalizedEuler_nonneg (n : ℕ) : 0 ≤ normalizedEuler n :=
  mul_nonneg (by norm_num) (expDivisorSum_nonneg (logParameter_nonneg n) n)

lemma normalizedEuler_prime {q : ℕ} (hq : q.Prime) : normalizedEuler q = 1 := by
  have he : expDivisorSum (logParameter q) q = (3 / 4 : ℝ) := by
    have hh := expDivisorSum_prime_pow (logParameter q) hq (by decide : 0 < 1)
    simpa only [pow_one, exp_logParameter hq.one_lt, show (1 : ℝ) - 1/4 = 3/4 by norm_num] using hh
  rw [normalizedEuler, he]
  norm_num

lemma normalizedEuler_composite_bound {n : ℕ} (hn : 1 < n) (hnp : ¬ n.Prime) :
    normalizedEuler n ≤ (2 / 3 : ℝ) := by
  have hb := primeProxy_composite_bound (logParameter_nonneg n) hn hnp
  rw [primeProxy, if_pos hn, exp_logParameter hn, exp_half_logParameter hn] at hb
  have hh := (div_le_iff₀ (euler_defect_pos (logParameter_nonneg n) hn)).mp hb
  unfold normalizedEuler
  linarith only [hh]

lemma logDetector_nonneg (n : ℕ) : 0 ≤ logDetector n := by
  unfold logDetector
  split_ifs
  · exact pow_nonneg (normalizedEuler_nonneg n) _
  · exact le_rfl

/-- The logarithmic-degree detector is exactly one at each prime. -/
theorem logDetector_prime {q : ℕ} (hq : q.Prime) : logDetector q = 1 := by
  simp only [logDetector, if_pos hq.one_lt, normalizedEuler_prime hq, one_pow]

/-- The error bound is global over all composites, not just prime-input floors. -/
theorem logDetector_composite_bound {n : ℕ} (hnp : ¬ n.Prime) :
    logDetector n ≤ ((n : ℝ)^2)⁻¹ := by
  by_cases hn : 1 < n
  · have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
    have hpow : (n : ℝ) ≤ (2 : ℝ)^(logSize n) := by
      exact_mod_cast (Nat.lt_pow_succ_log_self (by decide : 1 < 2) n).le
    rw [logDetector, if_pos hn]
    calc
      _ ≤ (2 / 3 : ℝ)^(logarithmicDegree n) :=
        pow_le_pow_left₀ (normalizedEuler_nonneg n) (normalizedEuler_composite_bound hn hnp) _
      _ = ((2 / 3 : ℝ)^4)^(logSize n) := by rw [logarithmicDegree, pow_mul]
      _ ≤ (1 / 4 : ℝ)^(logSize n) := pow_le_pow_left₀ (by norm_num) (by norm_num) _
      _ = (((2 : ℝ)^(logSize n))^2)⁻¹ := by
        rw [show (1 / 4 : ℝ) = ((2 : ℝ)^2)⁻¹ by norm_num, inv_pow, ← pow_mul,
          show 2 * logSize n = logSize n * 2 by omega, pow_mul]
      _ ≤ _ := by
        simpa only [one_div] using one_div_le_one_div_of_le (sq_pos_of_pos hnR)
          (pow_le_pow_left₀ hnR.le hpow 2)
  · simp only [logDetector, if_neg hn]
    positivity

noncomputable def compositeError (n : ℕ) : ℝ := if n.Prime then 0 else logDetector n

lemma compositeError_nonneg (n : ℕ) : 0 ≤ compositeError n := by
  unfold compositeError
  split_ifs
  · exact le_rfl
  · exact logDetector_nonneg n

theorem summable_compositeError : Summable compositeError := by
  apply (Real.summable_nat_pow_inv.mpr (by decide : 1 < 2)).of_nonneg_of_le compositeError_nonneg
  intro n
  unfold compositeError
  split_ifs with hn
  · positivity
  · exact logDetector_composite_bound hn

noncomputable def primeInputDetector (α : ℝ) (n : ℕ) : ℝ :=
  if n.Prime then logDetector (floorMul α n) else 0

noncomputable def inputError (α : ℝ) (n : ℕ) : ℝ :=
  primeInputDetector α n - primePairIndicator α n

lemma inputError_bounds (α : ℝ) (n : ℕ) :
    0 ≤ inputError α n ∧ inputError α n ≤ compositeError (floorMul α n) := by
  classical
  by_cases hp : n.Prime
  · by_cases hq : (floorMul α n).Prime
    · simp [inputError, primeInputDetector, primePairIndicator, compositeError, hp, hq,
        logDetector_prime hq]
    · simp only [inputError, primeInputDetector, primePairIndicator, compositeError,
        hp, hq, and_false, if_false, if_true, sub_zero]
      exact ⟨logDetector_nonneg _, le_rfl⟩
  · simpa only [inputError, primeInputDetector, primePairIndicator, hp, false_and,
      if_false, sub_self] using
      And.intro (le_refl (0 : ℝ)) (compositeError_nonneg (floorMul α n))

theorem summable_inputError {α : ℝ} (hα : 1 ≤ α) : Summable (inputError α) := by
  have hs := summable_compositeError.comp_injective (floorMul_strictMono hα).injective
  exact hs.of_nonneg_of_le (fun n => (inputError_bounds α n).1) (fun n => (inputError_bounds α n).2)

/-- Nonsummability of this logarithmic-degree detector is an exact reformulation
of infinitude, not a stronger weighted-divergence target. It is not proved here
at prescribed irrational slopes. -/
theorem summable_primeInputDetector_iff_finite {α : ℝ} (hα : 1 ≤ α) :
    Summable (primeInputDetector α) ↔
      {p : ℕ | p.Prime ∧ (floorMul α p).Prime}.Finite := by
  classical
  constructor
  · intro hs
    have he := (tendsto_order.mp hs.tendsto_atTop_zero).2 1 zero_lt_one
    obtain ⟨B, hB⟩ := eventually_atTop.mp he
    apply (Set.finite_Iio B).subset
    intro p hp
    change p < B
    by_contra hnot
    have hh := hB p (le_of_not_gt hnot)
    rw [primeInputDetector, if_pos hp.1, logDetector_prime hp.2] at hh
    exact (lt_irrefl 1) hh
  · intro hfin
    have hg : Summable (primePairIndicator α) := by
      apply summable_of_ne_finset_zero (s := hfin.toFinset)
      intro n hn
      have hnot : ¬ (n.Prime ∧ (floorMul α n).Prime) := by
        simpa only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] using hn
      simp [primePairIndicator, hnot]
    apply (hg.add (summable_inputError hα)).congr
    intro n
    unfold inputError
    ring

#print axioms logDetector_prime
#print axioms logDetector_composite_bound
#print axioms summable_compositeError
#print axioms summable_primeInputDetector_iff_finite

end Erdos972LogDegreePrimeDetector
