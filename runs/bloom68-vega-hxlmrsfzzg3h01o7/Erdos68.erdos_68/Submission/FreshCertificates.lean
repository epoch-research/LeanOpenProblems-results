import Mathlib

namespace FreshFactorialCertificates

set_option maxRecDepth 30000
set_option maxHeartbeats 10000000

/-- An exact modular certificate; no numerical approximation to the infinite sum. -/
lemma roots_mod_139 :
    (Finset.Icc 2 137).filter (fun n => (n.factorial - 1) % 139 = 0) =
      ({69, 122, 137} : Finset ℕ) := by decide

lemma units_mod_139 :
    ((69).factorial - 1) / 139 % 139 = 6 ∧
    ((122).factorial - 1) / 139 % 139 = 49 ∧
    ((137).factorial - 1) / 139 % 139 = 73 := by decide

lemma prime_139 : Nat.Prime 139 := by norm_num

lemma cancellation_mod_139 :
    (6 * 49 + 6 * 73 + 49 * 73 : ℕ) = 139 * 31 ∧
      (6 * 49 * 73 : ℕ) % 139 ≠ 0 := by decide

/-- Consecutive denominators are coprime, but the full sequence is not pairwise coprime. -/
lemma nonconsecutive_common_factor :
    23 ∣ ((4).factorial - 1) ∧ 23 ∣ ((8).factorial - 1) := by decide


/-- A rational finite sum using ordinary field division, not natural division. -/
def rationalPartial (N : ℕ) : ℚ :=
  ∑ n ∈ Finset.Icc 2 N, 1 / ((n.factorial : ℚ) - 1)

def integerLCM (N : ℕ) : ℕ :=
  (Finset.Icc 2 N).lcm (fun n => n.factorial - 1)

lemma denominator_loses_139 : (rationalPartial 137).den % 139 ≠ 0 := by decide +kernel

lemma exact_lcm_cancellation :
    integerLCM 137 = 139 * (rationalPartial 137).den := by decide +kernel

lemma ordinary_factorial_does_not_clear :
    (24 : ℚ) * rationalPartial 4 = 3432 / 115 ∧
      ((24 : ℚ) * rationalPartial 4).den = 115 := by decide +kernel

end FreshFactorialCertificates
