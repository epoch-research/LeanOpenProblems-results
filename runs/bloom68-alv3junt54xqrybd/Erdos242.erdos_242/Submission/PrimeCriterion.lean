import Submission.Bounds
import Submission.Certificates

/-!
# A necessary and sufficient prime certificate

For a prime `p ≡ 1 (mod 4)`, the positive, strictly ordered unit-fraction
statement `Erdos242Aux.Distinct p` is equivalent to the disjunction of the two
arithmetic certificates from `Submission.Certificates`.

`Distinct` is the exact ordered-denominator predicate already defined in
`Submission.Reduction`, imported through the two modules above.  This file
proves a criterion for each individual prime; it does not assert that every
prime has a certificate.
-/

namespace Erdos242Aux

/-- The two arithmetic certificates, with the necessary bounds on `x`. -/
def PrimeCertificate (p : ℕ) : Prop :=
  ∃ x d : ℕ, 0 < x ∧ 0 < d ∧ p < 4 * x ∧ 2 * x < p ∧ d ∣ x ^ 2 ∧
    ((4 * x - p) ∣ (4 * d + 1) ∨ (d < x ∧ (4 * x - p) ∣ (x + d)))

/-- Factoring a positive two-term reciprocal equation after clearing denominators.
Both subtractions are exact, and their product is the square of the numerator. -/
lemma solution_gap_factorization (m N y z : ℕ) (hN : 0 < N)
    (hy : 0 < y) (hz : 0 < z) (heq : m * y * z = N * (y + z)) :
    0 < m * y - N ∧ 0 < m * z - N ∧
      (m * y - N) * (m * z - N) = N ^ 2 := by
  have hNy : N < m * y := by
    have hprod : N * z < (m * y) * z := by
      calc
        N * z < N * (y + z) := Nat.mul_lt_mul_of_pos_left (by omega) hN
        _ = (m * y) * z := heq.symm
    exact Nat.lt_of_mul_lt_mul_right hprod
  have hNz : N < m * z := by
    have hprod : N * y < (m * z) * y := by
      calc
        N * y < N * (y + z) := Nat.mul_lt_mul_of_pos_left (by omega) hN
        _ = m * y * z := heq.symm
        _ = (m * z) * y := by ring
    exact Nat.lt_of_mul_lt_mul_right hprod
  have hAy : (m * y - N) + N = m * y := Nat.sub_add_cancel hNy.le
  have hBz : (m * z - N) + N = m * z := Nat.sub_add_cancel hNz.le
  have hfactor : (m * y) * (m * z) = N * (m * y + m * z) := by
    calc
      (m * y) * (m * z) = m * (m * y * z) := by ring
      _ = m * (N * (y + z)) := by rw [heq]
      _ = N * (m * y + m * z) := by ring
  have hfactor' : ((m * y - N) + N) * ((m * z - N) + N) =
      N * (((m * y - N) + N) + ((m * z - N) + N)) := by
    simpa only [hAy, hBz] using hfactor
  refine ⟨by omega, by omega, ?_⟩
  nlinarith only [hfactor']

/-- Every strictly ordered solution for a prime congruent to one modulo four
supplies one of the two certificates for its first denominator. -/
theorem prime_solution_certificate {p x y z : ℕ} (hp : p.Prime)
    (hp4 : p % 4 = 1) (hx : 1 ≤ x) (hxy : x < y) (hyz : y < z)
    (heq : (4 / p : ℚ) = 1 / x + 1 / y + 1 / z) :
    ∃ d : ℕ, 0 < d ∧ d ∣ x ^ 2 ∧
      ((4 * x - p) ∣ (4 * d + 1) ∨ (d < x ∧ (4 * x - p) ∣ (x + d))) := by
  obtain ⟨hpx, hxp, hxltp⟩ := prime_solution_bounds hp hp4 hx hxy hyz heq
  let m := 4 * x - p
  let N := p * x
  let A := m * y - N
  let B := m * z - N
  have hxpos : 0 < x := by omega
  have hNpos : 0 < N := Nat.mul_pos hp.pos hxpos
  have hsum : m + p = 4 * x := by dsimp only [m]; omega
  obtain ⟨_, _, _, _, hmx, hmp⟩ := certificate_modulus_facts p x hp hp4 hpx hxp
  change Nat.Coprime m x at hmx
  change Nat.Coprime m p at hmp
  have hcross := solution_cross_mul hp.pos hx hxy hyz heq
  have hgap : m * y * z = N * (y + z) := by
    rw [← hsum] at hcross
    dsimp only [N]
    nlinarith only [hcross]
  obtain ⟨hApos, _, hAB⟩ := solution_gap_factorization m N y z hNpos
    (by omega) (by omega) hgap
  change 0 < A at hApos
  change A * B = N ^ 2 at hAB
  have hAy : A + N = m * y := by
    dsimp only [A]
    have : N < m * y := by omega
    exact Nat.sub_add_cancel this.le
  have hAltN : A < N := by
    have hbound : m * y < 2 * N := by
      simpa only [m, N, Nat.mul_assoc] using
        second_mul_gap_lt hp.pos hx hxy hyz heq
    omega
  have hAdv : A ∣ p ^ 2 * x ^ 2 := by
    refine ⟨B, ?_⟩
    simpa only [N, mul_pow] using hAB.symm
  have hmNA : m ∣ N + A := by
    refine ⟨y, ?_⟩
    omega
  by_cases hpA : p ∣ A
  · obtain ⟨d, hpd⟩ := hpA
    have hdpos : 0 < d := by
      by_contra hd
      have hd0 : d = 0 := by omega
      simp only [hd0, mul_zero] at hpd
      omega
    have hdx : d < x := (Nat.mul_lt_mul_left hp.pos).mp
      (by simpa only [hpd, N] using hAltN)
    have hpnd : ¬ p ∣ d := Nat.not_dvd_of_pos_of_lt hdpos (lt_trans hdx hxltp)
    have hdcop : Nat.Coprime d p := (hp.coprime_iff_not_dvd.mpr hpnd).symm
    have hdivdp : d ∣ p * x ^ 2 := by
      have h : p * d ∣ p * (p * x ^ 2) := by
        simpa only [hpd, pow_two, Nat.mul_assoc] using hAdv
      exact Nat.dvd_of_mul_dvd_mul_left hp.pos h
    have hdvd : d ∣ x ^ 2 := hdcop.dvd_of_dvd_mul_left hdivdp
    have hmxd : m ∣ x + d := by
      apply hmp.dvd_of_dvd_mul_left
      have hrew : N + A = p * (x + d) := by dsimp only [N]; rw [hpd]; ring
      rw [← hrew]
      exact hmNA
    exact ⟨d, hdpos, hdvd, Or.inr ⟨hdx, hmxd⟩⟩
  · have hAcop : Nat.Coprime A (p ^ 2) := hp.coprime_pow_of_not_dvd hpA
    have hAx2 : A ∣ x ^ 2 := hAcop.dvd_of_dvd_mul_left hAdv
    let d := x ^ 2 / A
    have hdpos : 0 < d :=
      positive_quotient_of_dvd (x ^ 2) A (by positivity) hApos hAx2
    have hAd : A * d = x ^ 2 := Nat.mul_div_cancel' hAx2
    have hdvd : d ∣ x ^ 2 := ⟨A, by rw [← hAd]; ring⟩
    have hprod : (N + A) * d = x * (p * d + x) := by
      calc
        (N + A) * d = p * x * d + A * d := by dsimp only [N]; ring
        _ = x * (p * d + x) := by rw [hAd]; ring
    have hmpdx : m ∣ p * d + x := by
      apply hmx.dvd_of_dvd_mul_left
      rw [← hprod]
      exact dvd_mul_of_dvd_left hmNA d
    have h4eq : m + p * (4 * d + 1) = 4 * (p * d + x) := by
      calc
        m + p * (4 * d + 1) = (m + p) + 4 * p * d := by ring
        _ = 4 * (p * d + x) := by rw [hsum]; ring
    have hdivp : m ∣ p * (4 * d + 1) := by
      apply (Nat.dvd_add_iff_right (dvd_refl m)).mpr
      rw [h4eq]
      exact dvd_mul_of_dvd_right hmpdx 4
    have hdiv : m ∣ 4 * d + 1 := hmp.dvd_of_dvd_mul_left hdivp
    exact ⟨d, hdpos, hdvd, Or.inl hdiv⟩

/-- The exact necessary-and-sufficient criterion for an individual prime
congruent to one modulo four. -/
theorem prime_distinct_iff_certificate (p : ℕ) (hp : p.Prime) (hp4 : p % 4 = 1) :
    Distinct p ↔ ∃ x d : ℕ, 0 < x ∧ 0 < d ∧ p < 4 * x ∧ 2 * x < p ∧ d ∣ x ^ 2 ∧
      ((4 * x - p) ∣ (4 * d + 1) ∨ (d < x ∧ (4 * x - p) ∣ (x + d))) := by
  constructor
  · rintro ⟨x, y, z, hx, hxy, hyz, heq⟩
    obtain ⟨hpx, hxp, _⟩ := prime_solution_bounds hp hp4 hx hxy hyz heq
    obtain ⟨d, hd, hdvd, hcert⟩ := prime_solution_certificate hp hp4 hx hxy hyz heq
    exact ⟨x, d, by omega, hd, hpx, hxp, hdvd, hcert⟩
  · rintro ⟨x, d, hx, hd, hpx, hxp, hdvd, hcert⟩
    rcases hcert with hI | ⟨hdx, hII⟩
    · exact certificate_I p x d hp hp4 hx hd hpx hxp hdvd hI
    · exact certificate_II p x d hp hp4 hx hd hpx hxp hdvd hdx hII

/-- The same prime criterion using the named certificate predicate. -/
theorem prime_distinct_iff_primeCertificate (p : ℕ) (hp : p.Prime)
    (hp4 : p % 4 = 1) : Distinct p ↔ PrimeCertificate p :=
  prime_distinct_iff_certificate p hp hp4

/-- Both certificate parameters can be searched over explicit finite intervals.
This is an equivalence for each prime, not a claim that the search succeeds. -/
theorem prime_distinct_iff_bounded_certificate (p : ℕ) (hp : p.Prime)
    (hp4 : p % 4 = 1) :
    Distinct p ↔
      ∃ x ∈ Finset.Icc (p / 4 + 1) ((p - 1) / 2),
        ∃ d ∈ Finset.Icc 1 (x ^ 2), d ∣ x ^ 2 ∧
          ((4 * x - p) ∣ (4 * d + 1) ∨ (d < x ∧ (4 * x - p) ∣ (x + d))) := by
  rw [prime_distinct_iff_certificate p hp hp4]
  constructor
  · rintro ⟨x, d, hx, hd, hpx, hxp, hdvd, hcert⟩
    refine ⟨x, Finset.mem_Icc.mpr ⟨?_, ?_⟩, d,
      Finset.mem_Icc.mpr ⟨by omega, Nat.le_of_dvd (by positivity) hdvd⟩, hdvd, hcert⟩
    all_goals omega
  · rintro ⟨x, hx, d, hd, hdvd, hcert⟩
    obtain ⟨hxlo, hxhi⟩ := Finset.mem_Icc.mp hx
    obtain ⟨hdlo, _⟩ := Finset.mem_Icc.mp hd
    have hppos := hp.pos
    exact ⟨x, d, by omega, by omega, by omega, by omega, hdvd, hcert⟩

/-- Failure of `Distinct p` is exactly failure of every certificate in the
explicit finite search.  No uniform existence or nonexistence is asserted. -/
theorem prime_not_distinct_iff_finite_check (p : ℕ) (hp : p.Prime)
    (hp4 : p % 4 = 1) :
    ¬ Distinct p ↔
      ∀ x ∈ Finset.Icc (p / 4 + 1) ((p - 1) / 2),
        ∀ d ∈ Finset.Icc 1 (x ^ 2),
          ¬ (d ∣ x ^ 2 ∧
            ((4 * x - p) ∣ (4 * d + 1) ∨ (d < x ∧ (4 * x - p) ∣ (x + d)))) := by
  rw [prime_distinct_iff_bounded_certificate p hp hp4]
  simp only [not_exists, not_and]

end Erdos242Aux
