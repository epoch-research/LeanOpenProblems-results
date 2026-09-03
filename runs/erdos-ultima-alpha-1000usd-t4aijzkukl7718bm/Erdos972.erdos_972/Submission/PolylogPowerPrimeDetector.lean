import Submission.PolylogMomentPrimeProxy

/-! A single polylogarithmic power of an adaptive Euler product approximates
the prime indicator, with a globally summable composite error. The exact
pointwise divergence required by Erdős 972 remains an unproved input. -/
namespace Erdos972PolylogPowerPrimeDetector

open Finset Filter
open scoped Topology
open Erdos972PolylogMomentPrimeProxy Erdos972NonlinearPrimeProxy
open Erdos972CriticalNonlinearPrimeProxy
open Erdos972SmoothMangoldt Erdos972SmoothMangoldtPositive Erdos972PrimePowerError

set_option autoImplicit false
set_option maxHeartbeats 2000000

def powerBudget (n : ℕ) : ℕ := (logSize n)^6

noncomputable def powerDetector (n : ℕ) : ℝ :=
  if 1 < n then (expDivisorSum (parameter n) n)^(powerBudget n) else 0

lemma two_le_logSize {n : ℕ} (hn : 1 < n) : 2 ≤ logSize n := by
  have hh := Nat.log_pos (by decide : 1 < 2) (by omega : 2 ≤ n)
  unfold logSize
  omega

lemma log_le_logSize {n : ℕ} (hn : 0 < n) : Real.log n ≤ (logSize n : ℝ) := by
  have hp : (n : ℝ) ≤ (2 : ℝ)^(logSize n) := by
    exact_mod_cast (Nat.lt_pow_succ_log_self (by decide : 1 < 2) n).le
  have hh := Real.log_le_log (Nat.cast_pos.mpr hn) hp
  rw [Real.log_pow] at hh
  have h2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith only [h]
  exact hh.trans (by nlinarith only [mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg (logSize n))])

lemma powerDetector_nonneg (n : ℕ) : 0 ≤ powerDetector n := by
  unfold powerDetector
  split_ifs
  · exact pow_nonneg (expDivisorSum_nonneg (parameter_nonneg n) n) _
  · exact le_rfl

lemma powerDetector_le_one (n : ℕ) : powerDetector n ≤ 1 := by
  unfold powerDetector
  split_ifs with hn
  · exact pow_le_one₀ (expDivisorSum_nonneg (parameter_nonneg n) n)
      (by linarith only [euler_defect_pos (parameter_nonneg n) hn])
  · norm_num

/-- A single power with exponent (1+log_2 q)^6 retains at least three
quarters of the prime indicator's value. -/
theorem powerDetector_prime_lower {q : ℕ} (hq : q.Prime) :
    (3 / 4 : ℝ) ≤ powerDetector q := by
  have hL : (0 : ℝ) < logSize q := Nat.cast_pos.mpr (logSize_pos q)
  have hL2 : (2 : ℝ) ≤ logSize q := by exact_mod_cast two_le_logSize hq.one_lt
  have hx0 : 0 ≤ ((logSize q : ℝ)^8)⁻¹ := by positivity
  have hx1 : ((logSize q : ℝ)^8)⁻¹ ≤ 1 :=
    (inv_le_one₀ (by positivity)).mpr (one_le_pow₀ (by linarith))
  have he : expDivisorSum (parameter q) q = 1 - ((logSize q : ℝ)^8)⁻¹ := by
    simpa only [pow_one, exp_parameter hq.one_lt] using
      expDivisorSum_prime_pow (parameter q) hq (by decide : 0 < 1)
  have hBern : 1 - (powerBudget q : ℝ)*((logSize q : ℝ)^8)⁻¹ ≤
      (1 - ((logSize q : ℝ)^8)⁻¹)^(powerBudget q) := by
    simpa only [mul_neg, ← sub_eq_add_neg] using
      one_add_mul_le_pow (by linarith : -2 ≤ -((logSize q : ℝ)^8)⁻¹) (powerBudget q)
  have hcancel : (powerBudget q : ℝ)*((logSize q : ℝ)^8)⁻¹ = ((logSize q : ℝ)^2)⁻¹ := by
    simp only [powerBudget, Nat.cast_pow]
    field_simp
  have hinv : ((logSize q : ℝ)^2)⁻¹ ≤ (1 / 4 : ℝ) := by
    simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 4)
      (show (4 : ℝ) ≤ (logSize q : ℝ)^2 by nlinarith)
  rw [hcancel] at hBern
  rw [powerDetector, if_pos hq.one_lt, he]
  linarith only [hBern, hinv]

lemma composite_defect_lower {n : ℕ} (hn : 1 < n) (hnp : ¬ n.Prime) :
    ((logSize n : ℝ)^4)⁻¹ ≤ 1 - expDivisorSum (parameter n) n := by
  have hL : (0 : ℝ) < logSize n := Nat.cast_pos.mpr (logSize_pos n)
  have hb := primeProxy_composite_bound (parameter_nonneg n) hn hnp
  rw [primeProxy, if_pos hn, exp_parameter hn, exp_half_parameter hn] at hb
  have hh := (div_le_iff₀ (euler_defect_pos (parameter_nonneg n) hn)).mp hb
  have he : ((logSize n : ℝ)^8)⁻¹ = (((logSize n : ℝ)^4)⁻¹)^2 := by ring
  rw [he] at hh
  have hx : 0 < ((logSize n : ℝ)^4)⁻¹ := by positivity
  nlinarith only [hh, hx]

lemma powerDetector_composite_exp_bound {n : ℕ} (hn : 1 < n) (hnp : ¬ n.Prime) :
    powerDetector n ≤ Real.exp (-((logSize n : ℝ)^2)) := by
  have hL : (0 : ℝ) < logSize n := Nat.cast_pos.mpr (logSize_pos n)
  have hdef := composite_defect_lower hn hnp
  have hex := Real.add_one_le_exp (-((logSize n : ℝ)^4)⁻¹)
  have he : expDivisorSum (parameter n) n ≤ Real.exp (-((logSize n : ℝ)^4)⁻¹) := by
    linarith only [hdef, hex]
  rw [powerDetector, if_pos hn]
  apply (pow_le_pow_left₀ (expDivisorSum_nonneg (parameter_nonneg n) n) he (powerBudget n)).trans_eq
  rw [← Real.exp_nat_mul]
  congr 1
  simp only [powerBudget, Nat.cast_pow]
  field_simp

/-- The adaptive parameter and polylogarithmic power suppress every composite
by a summable square-reciprocal envelope. -/
theorem powerDetector_composite_bound {n : ℕ} (hnp : ¬ n.Prime) :
    powerDetector n ≤ ((n : ℝ)^2)⁻¹ := by
  by_cases hn : 1 < n
  · have hL : (2 : ℝ) ≤ logSize n := by exact_mod_cast two_le_logSize hn
    have hlog := log_le_logSize (by omega : 0 < n)
    apply (powerDetector_composite_exp_bound hn hnp).trans
    rw [← exp_neg_two_log (by omega : 0 < n)]
    apply Real.exp_le_exp.mpr
    nlinarith only [hL, hlog, sq_nonneg ((logSize n : ℝ) - 2)]
  · simp only [powerDetector, if_neg hn]
    positivity

noncomputable def compositePowerError (n : ℕ) : ℝ :=
  if n.Prime then 0 else powerDetector n

lemma compositePowerError_nonneg (n : ℕ) : 0 ≤ compositePowerError n := by
  unfold compositePowerError
  split_ifs
  · exact le_rfl
  · exact powerDetector_nonneg n

theorem summable_compositePowerError : Summable compositePowerError := by
  apply (Real.summable_nat_pow_inv.mpr (by decide : 1 < 2)).of_nonneg_of_le
    compositePowerError_nonneg
  intro n
  unfold compositePowerError
  split_ifs with hn
  · positivity
  · exact powerDetector_composite_bound hn

noncomputable def primeInputDetector (α : ℝ) (n : ℕ) : ℝ :=
  if n.Prime then powerDetector (floorMul α n) else 0

noncomputable def genuinePrimePart (α : ℝ) (n : ℕ) : ℝ :=
  if n.Prime ∧ (floorMul α n).Prime then powerDetector (floorMul α n) else 0

noncomputable def inputError (α : ℝ) (n : ℕ) : ℝ :=
  primeInputDetector α n - genuinePrimePart α n

lemma inputError_bounds (α : ℝ) (n : ℕ) :
    0 ≤ inputError α n ∧ inputError α n ≤ compositePowerError (floorMul α n) := by
  classical
  by_cases hp : n.Prime
  · by_cases hq : (floorMul α n).Prime
    · simp [inputError, primeInputDetector, genuinePrimePart, compositePowerError, hp, hq]
    · simp only [inputError, primeInputDetector, genuinePrimePart, compositePowerError,
        hp, hq, and_false, if_false, if_true, sub_zero]
      exact ⟨powerDetector_nonneg _, le_rfl⟩
  · simpa only [inputError, primeInputDetector, genuinePrimePart, hp, false_and,
      if_false, sub_self] using
      And.intro (le_refl (0 : ℝ)) (compositePowerError_nonneg (floorMul α n))

theorem summable_inputError {α : ℝ} (hα : 1 ≤ α) : Summable (inputError α) := by
  have hs := summable_compositePowerError.comp_injective (floorMul_strictMono hα).injective
  exact hs.of_nonneg_of_le (fun n => (inputError_bounds α n).1) (fun n => (inputError_bounds α n).2)

/-- This exact equivalence uses a single polylogarithmic moment, not a full
geometric series or a stronger weighted prime-pair divergence assumption.
Neither side is asserted for every prescribed irrational slope. -/
theorem summable_primeInputDetector_iff_finite {α : ℝ} (hα : 1 ≤ α) :
    Summable (primeInputDetector α) ↔
      {p : ℕ | p.Prime ∧ (floorMul α p).Prime}.Finite := by
  classical
  constructor
  · intro hs
    have he := (tendsto_order.mp hs.tendsto_atTop_zero).2 (3 / 4) (by norm_num)
    obtain ⟨B, hB⟩ := eventually_atTop.mp he
    apply (Set.finite_Iio B).subset
    intro p hp
    change p < B
    by_contra hnot
    have hh := hB p (le_of_not_gt hnot)
    rw [primeInputDetector, if_pos hp.1] at hh
    exact (not_lt_of_ge (powerDetector_prime_lower hp.2)) hh
  · intro hfin
    have hg : Summable (genuinePrimePart α) := by
      apply summable_of_ne_finset_zero (s := hfin.toFinset)
      intro n hn
      have hnot : ¬ (n.Prime ∧ (floorMul α n).Prime) := by
        simpa only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] using hn
      simp [genuinePrimePart, hnot]
    apply (hg.add (summable_inputError hα)).congr
    intro n
    unfold inputError
    ring

#print axioms powerDetector_prime_lower
#print axioms powerDetector_composite_bound
#print axioms summable_compositePowerError
#print axioms summable_primeInputDetector_iff_finite

end Erdos972PolylogPowerPrimeDetector
