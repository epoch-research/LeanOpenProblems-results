import Submission.LogDegreePrimeDetector
import Submission.GcdProfileExpansion

/-! The logarithmic-degree representation does not justify discarding large
divisors. At a prime output, the last divisor cancels a normalization factor
larger than the output itself. These are exact arithmetic identities, not a
counterexample to Erdős 972. -/
namespace Erdos972LogDegreeDivisorTail

open Finset ArithmeticFunction
open Erdos972LogDegreePrimeDetector Erdos972PolylogMomentPrimeProxy
open Erdos972SmoothMangoldt Erdos972GcdProfileExpansion

set_option autoImplicit false
set_option maxHeartbeats 2000000

noncomputable def normalization (n : ℕ) : ℝ := (4 / 3 : ℝ)^(logarithmicDegree n)

noncomputable def adaptiveCoeff (n d : ℕ) : ℝ :=
  profileCoeff (fun m => (expDivisorSum (logParameter n) m)^(logarithmicDegree n)) d

noncomputable def truncatedDetector (D n : ℕ) : ℝ :=
  normalization n * ∑ d ∈ n.divisors.filter (fun d => d ≤ D), adaptiveCoeff n d

lemma normalization_pos (n : ℕ) : 0 < normalization n := by unfold normalization; positivity

/-- The normalization in this particular logarithmic-degree construction grows
faster than n. This is not an estimate for the already normalized detector. -/
lemma self_lt_normalization (n : ℕ) : (n : ℝ) < normalization n := by
  have hn : (n : ℝ) < (2 : ℝ)^(logSize n) := by
    exact_mod_cast Nat.lt_pow_succ_log_self (by decide : 1 < 2) n
  apply hn.trans_le
  unfold normalization logarithmicDegree
  rw [pow_mul]
  exact pow_le_pow_left₀ (by norm_num) (by norm_num) _

lemma adaptiveCoeff_one (n : ℕ) : adaptiveCoeff n 1 = 1 := by
  simp [adaptiveCoeff, profileCoeff_eq_sum, expDivisorSum]

/-- Exact finite Mobius inversion, including all divisors of the output. -/
theorem full_divisor_identity {n : ℕ} (hn : 1 < n) :
    logDetector n = normalization n * ∑ d ∈ n.divisors, adaptiveCoeff n d := by
  rw [logDetector, if_pos hn, normalizedEuler, mul_pow]
  change normalization n * (expDivisorSum (logParameter n) n)^(logarithmicDegree n) = _
  congr 1
  exact (sum_profileCoeff (fun m => (expDivisorSum (logParameter n) m)^(logarithmicDegree n))
    (by omega : n ≠ 0)).symm

/-- At a prime output the omitted last divisor supplies the large negative
coefficient needed to reduce the normalization to the exact value one. -/
theorem prime_last_divisor_cancellation {q : ℕ} (hq : q.Prime) :
    normalization q * adaptiveCoeff q q = 1 - normalization q := by
  have hh := full_divisor_identity hq.one_lt
  rw [logDetector_prime hq] at hh
  have hsum : (∑ d ∈ q.divisors, adaptiveCoeff q d) = 1 + adaptiveCoeff q q := by
    simp [hq.divisors, hq.ne_one.symm, adaptiveCoeff_one]
  rw [hsum] at hh
  nlinarith only [hh]

lemma truncatedDetector_prime {q D : ℕ} (hq : q.Prime) (hD : 1 ≤ D) (hDq : D < q) :
    truncatedDetector D q = normalization q := by
  have hfilter : q.divisors.filter (fun d => d ≤ D) = {1} := by
    ext d
    simp only [mem_filter, hq.divisors, mem_insert, mem_singleton]
    omega
  rw [truncatedDetector, hfilter, sum_singleton, adaptiveCoeff_one, mul_one]

theorem prime_truncation_error {q D : ℕ} (hq : q.Prime) (hD : 1 ≤ D) (hDq : D < q) :
    |truncatedDetector D q - logDetector q| = normalization q - 1 := by
  rw [truncatedDetector_prime hq hD hDq, logDetector_prime hq]
  apply abs_of_nonneg
  have hh := self_lt_normalization q
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq.one_le
  linarith only [hh, hqR]

/-- A proper-divisor cutoff has error greater than q-1 on every prime q.
Small degree alone therefore supplies no pointwise small-tail estimate. -/
theorem prime_truncation_error_large {q D : ℕ} (hq : q.Prime) (hD : 1 ≤ D) (hDq : D < q) :
    (q : ℝ) - 1 < |truncatedDetector D q - logDetector q| := by
  rw [prime_truncation_error hq hD hDq]
  linarith only [self_lt_normalization q]

/-- For every fixed cutoff, the actual truncation error is unbounded on prime
outputs. This does not rule out an averaged signed cancellation argument. -/
theorem unbounded_prime_truncation_error {D : ℕ} (hD : 1 ≤ D) (B : ℕ) :
    ∃ q : ℕ, q.Prime ∧ D < q ∧ (B : ℝ) < |truncatedDetector D q - logDetector q| := by
  obtain ⟨q, hqB, hq⟩ := Nat.exists_infinite_primes (max D B + 2)
  have hDq : D < q := by omega
  have hBq : B + 1 ≤ q := by omega
  have hcast : (B : ℝ) + 1 ≤ q := by exact_mod_cast hBq
  refine ⟨q, hq, hDq, ?_⟩
  exact (by linarith only [hcast] : (B : ℝ) ≤ (q : ℝ) - 1).trans_lt
    (prime_truncation_error_large hq hD hDq)

/-- Even the squared-error mean cannot be controlled uniformly by a fixed
proper-divisor cutoff: one prime output already supplies this lower bound. -/
theorem prime_truncation_energy_lower {q D : ℕ} (hq : q.Prime) (hD : 1 ≤ D) (hDq : D < q) :
    ((q : ℝ) - 1)^2 <
      ∑ n ∈ Ioc 0 q, (truncatedDetector D n - logDetector n)^2 := by
  have he := prime_truncation_error_large hq hD hDq
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq.one_le
  have hs : ((q : ℝ) - 1)^2 < (truncatedDetector D q - logDetector q)^2 := by
    have hh := (sq_lt_sq₀ (by linarith : 0 ≤ (q : ℝ) - 1) (abs_nonneg _)).mpr he
    simpa only [sq_abs] using hh
  exact hs.trans_le (single_le_sum (fun n _ => sq_nonneg (truncatedDetector D n - logDetector n))
    (mem_Ioc.mpr ⟨hq.pos, le_rfl⟩))

/-- This rules out the direct adaptive-detector analogue of a uniform L2
small-divisor-tail estimate. It says nothing about signed cancellation. -/
theorem no_fixed_uniform_energy_cutoff {D : ℕ} (hD : 1 ≤ D) (C : ℝ) :
    ∃ N : ℕ, 0 < N ∧ C * N <
      ∑ n ∈ Ioc 0 N, (truncatedDetector D n - logDetector n)^2 := by
  obtain ⟨B, hB⟩ := exists_nat_gt (C + 3)
  obtain ⟨q, hqB, hq⟩ := Nat.exists_infinite_primes (max D B + 1)
  have hDq : D < q := by omega
  have hBq : (B : ℝ) ≤ q := Nat.cast_le.mpr (by omega)
  have hqR : (0 : ℝ) < q := Nat.cast_pos.mpr hq.pos
  have hprod : 0 < (q : ℝ) * ((q : ℝ) - 2 - C) :=
    mul_pos hqR (by linarith only [hB, hBq])
  refine ⟨q, hq.pos, ?_⟩
  exact (by nlinarith only [hprod] : C * (q : ℝ) < ((q : ℝ) - 1)^2).trans
    (prime_truncation_energy_lower hq hD hDq)

#print axioms prime_truncation_energy_lower
#print axioms no_fixed_uniform_energy_cutoff
#print axioms full_divisor_identity
#print axioms prime_last_divisor_cancellation
#print axioms prime_truncation_error_large
#print axioms unbounded_prime_truncation_error

end Erdos972LogDegreeDivisorTail
