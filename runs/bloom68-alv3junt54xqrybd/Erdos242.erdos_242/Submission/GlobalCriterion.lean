import Submission.PrimeCriterion
import Submission.NormSheets

/-!
# The remaining universal certificate assertion

This module identifies the universal ordered-denominator statement with uniform
existence of the arithmetic certificate on primes congruent to one modulo
24. It proves an equivalence, not either side of that equivalence.
-/

namespace Erdos242Aux

/-- The exact universal problem reduced to certificates on the remaining primes. -/
theorem universal_distinct_iff_primeCertificates :
    (∀ n : ℕ, 2 < n → Distinct n) ↔
      (∀ p : ℕ, p.Prime → p % 24 = 1 → PrimeCertificate p) := by
  constructor
  · intro h p hp hp24
    have hp2 : 2 < p := by have := hp.two_le; omega
    have hp4 : p % 4 = 1 := by omega
    exact (prime_distinct_iff_primeCertificate p hp hp4).mp (h p hp2)
  · intro h
    apply prime_one_mod_twentyfour_reduction.mpr
    intro p hp hp24
    have hp2 : 2 < p := by have := hp.two_le; omega
    have hp4 : p % 4 = 1 := by omega
    apply (ordinary_iff_distinct p hp2).mpr
    exact (prime_distinct_iff_primeCertificate p hp hp4).mpr (h p hp hp24)

/-- Any failure of the universal statement supplies a failing prime certificate.
This is an equivalence of negations, not an assertion that a failure exists. -/
theorem not_universal_iff_prime_counterexample :
    (¬ ∀ n : ℕ, 2 < n → Distinct n) ↔
      ∃ p : ℕ, p.Prime ∧ p % 24 = 1 ∧ ¬ PrimeCertificate p := by
  rw [universal_distinct_iff_primeCertificates]
  simp only [not_forall, exists_prop]

/-- An equivalent uniform assertion in the full Rosati normal forms. -/
theorem universal_distinct_iff_fullRosati :
    (∀ n : ℕ, 2 < n → Distinct n) ↔
      (∀ p : ℕ, p.Prime → p % 24 = 1 → FullI p ∨ FullII p) := by
  apply universal_distinct_iff_primeCertificates.trans
  constructor
  · intro h p hp hp24
    exact (primeCertificate_iff_full_rosati hp (by omega)).mp (h p hp hp24)
  · intro h p hp hp24
    exact (primeCertificate_iff_full_rosati hp (by omega)).mpr (h p hp hp24)

/-- An equivalent uniform assertion in the exact positive factor sheets. -/
theorem universal_distinct_iff_normSheets :
    (∀ n : ℕ, 2 < n → Distinct n) ↔
      (∀ p : ℕ, p.Prime → p % 24 = 1 → NormI p ∨ LiftII p) := by
  apply universal_distinct_iff_primeCertificates.trans
  constructor
  · intro h p hp hp24
    exact (primeCertificate_iff_full_patterns hp (by omega)).mp (h p hp hp24)
  · intro h p hp hp24
    exact (primeCertificate_iff_full_patterns hp (by omega)).mpr (h p hp hp24)

/-- A failure supplies a prime missing both sheets; failure is not asserted. -/
theorem not_universal_iff_normSheet_counterexample :
    (¬ ∀ n : ℕ, 2 < n → Distinct n) ↔
      ∃ p : ℕ, p.Prime ∧ p % 24 = 1 ∧ ¬ NormI p ∧ ¬ LiftII p := by
  rw [universal_distinct_iff_normSheets]
  simp only [not_forall, exists_prop, not_or]

end Erdos242Aux
