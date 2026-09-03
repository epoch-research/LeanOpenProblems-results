import FormalConjecturesUtil

/-!
# Exact scaling identities for the Erdős 371 ordering observable

These are finite auxiliary identities, not a proof of natural-density
cancellation. In particular, the dyadic identity retains a conditional weight.
-/

namespace Erdos371Scaling

/-- The signed comparison of two natural numbers. -/
def orientation (a b : ℕ) : ℤ := if a < b then 1 else if b < a then -1 else 0

/-- Subdividing an edge retains its direction only when the midpoint lies between its ends. -/
theorem orientation_subdivision (a b c : ℕ) (hab : a ≠ b) (hbc : b ≠ c) :
    orientation a b + orientation b c =
      if min a c < b ∧ b < max a c then 2 * orientation a c else 0 := by
  unfold orientation
  split_ifs <;> simp_all only [min_def, max_def] <;> split_ifs at * <;> omega

/-- Adjacent nontrivial integers have different largest prime factors. -/
theorem maxPrimeFac_succ_ne {n : ℕ} (hn : 1 < n) :
    Nat.maxPrimeFac (n + 1) ≠ Nat.maxPrimeFac n := by
  intro heq
  have hp := Nat.prime_maxPrimeFac_of_one_lt n hn
  have hd : Nat.maxPrimeFac n ∣ n + 1 := by
    rw [← heq]
    exact Nat.maxPrimeFac_dvd
  exact hp.not_dvd_one (by simpa using Nat.dvd_sub hd Nat.maxPrimeFac_dvd)

/-- A multiplier with no larger prime factor leaves the greatest prime factor unchanged. -/
theorem maxPrimeFac_mul_eq {k n : ℕ} (hk : k ≠ 0) (hn : n ≠ 0)
    (h : Nat.maxPrimeFac k ≤ Nat.maxPrimeFac n) :
    Nat.maxPrimeFac (k * n) = Nat.maxPrimeFac n := by
  rw [Nat.maxPrimeFac_mul hk hn, max_eq_right h]

/-- The same exceptional set works simultaneously for all positive multipliers at most `K`. -/
theorem maxPrimeFac_mul_eq_of_le {K k n : ℕ} (hk : 0 < k) (hkK : k ≤ K)
    (hn : K < Nat.maxPrimeFac n) : Nat.maxPrimeFac (k * n) = Nat.maxPrimeFac n := by
  have hn0 : n ≠ 0 := by
    intro h
    simp [h] at hn
  apply maxPrimeFac_mul_eq (by omega) hn0
  exact (Nat.le_of_dvd hk Nat.maxPrimeFac_dvd).trans (hkK.trans hn.le)

/-- Doubling a nontrivial integer does not change its greatest prime factor. -/
theorem maxPrimeFac_double {n : ℕ} (hn : 1 < n) :
    Nat.maxPrimeFac (2 * n) = Nat.maxPrimeFac n := by
  apply maxPrimeFac_mul_eq (by decide) (by omega)
  simpa only [Nat.prime_two.maxPrimeFac_eq_self] using
    (Nat.prime_maxPrimeFac_of_one_lt n hn).two_le

/-- The exact signed ordering observable for consecutive integers. -/
def signedComparison (n : ℕ) : ℤ :=
  orientation (Nat.maxPrimeFac n) (Nat.maxPrimeFac (n + 1))

/-- Exact dyadic refinement. The nonconstant middle-value condition cannot be discarded. -/
theorem signedComparison_double {n : ℕ} (hn : 1 < n) :
    signedComparison (2 * n) + signedComparison (2 * n + 1) =
      if min (Nat.maxPrimeFac n) (Nat.maxPrimeFac (n + 1)) <
          Nat.maxPrimeFac (2 * n + 1) ∧
        Nat.maxPrimeFac (2 * n + 1) <
          max (Nat.maxPrimeFac n) (Nat.maxPrimeFac (n + 1))
      then 2 * signedComparison n else 0 := by
  have h₀ := maxPrimeFac_succ_ne (n := 2 * n) (by omega)
  have h₁ := maxPrimeFac_succ_ne (n := 2 * n + 1) (by omega)
  have hd₀ := maxPrimeFac_double hn
  have hd₁ : Nat.maxPrimeFac (2 * n + 1 + 1) = Nat.maxPrimeFac (n + 1) := by
    exact maxPrimeFac_double (n := n + 1) (by omega)
  have h := orientation_subdivision
    (Nat.maxPrimeFac (2 * n)) (Nat.maxPrimeFac (2 * n + 1))
    (Nat.maxPrimeFac (2 * n + 1 + 1)) h₀.symm h₁.symm
  simpa only [signedComparison, hd₀, hd₁] using h

/-- A triadic path need not have the direction of its endpoints. -/
example : orientation 2 1 + orientation 1 0 + orientation 0 3 = -1 ∧
    orientation 2 3 = 1 := by decide

#print axioms maxPrimeFac_mul_eq_of_le
#print axioms signedComparison_double

end Erdos371Scaling
