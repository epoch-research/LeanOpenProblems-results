import Submission.GaussianNormBarrier

/-!
# Eisenstein and paired Gaussian/Eisenstein norm-coordinate barriers

Suppose `p = A² - A*B + B²` is a hard prime, written without subtraction as
`A = B + C` and `p = B² + A*C`, with `B,C > 0`. Every prime dividing
`A*B*C` is a quadratic residue modulo `p`. The same is true of Gaussian
coordinate factors, so using *products of either norm's axes* cannot supply
either of the complete first-denominator divisor certificates. This is only a
pointwise obstruction, NOT a proof or disproof of Erdős–Straus.

Existence of Eisenstein coordinates for primes `p ≡ 1 mod 3` is not needed
by (and is not asserted in) the conditional theorems below. `Spec.lean` is
neither imported nor changed.
-/

namespace Erdos242

/-- If a prime `ell` divides the product term in `p = s² + t*u`, then
`(ell/p)=+1` for `p ≡ 1 mod 8`. For an odd `ell`, `p` is a *nonzero*
square modulo `ell` and reciprocity applies. -/
theorem square_plus_product_prime_factor_residue (p s t u ell : ℕ)
    (hpp : p.Prime) (hp8 : p % 8 = 1)
    (hs : 0 < s) (ht : 0 < t) (hu : 0 < u)
    (hrep : p = s ^ 2 + t * u) (hell : ell.Prime) (hdiv : ell ∣ t * u) :
    jacobiSym (ell : ℤ) p = 1 := by
  rcases hell.eq_two_or_odd' with htwo | hellodd
  · subst ell
    have hpodd : Odd p := Nat.odd_iff.mpr (by omega)
    change jacobiSym (2 : ℤ) p = 1
    rw [jacobiSym.at_two hpodd, ZMod.χ₈_nat_eq_if_mod_eight]
    have hp2 : p % 2 = 1 := by omega
    simp [hp2, hp8]
  · have htlp : t < p := by
      have hle : t ≤ t * u := by
        simpa only [mul_one] using Nat.mul_le_mul_left t (show 1 ≤ u by omega)
      have hpos : 0 < s ^ 2 := pow_pos hs _
      omega
    have hulp : u < p := by
      have hle : u ≤ t * u := by
        simpa only [one_mul] using Nat.mul_le_mul_right u (show 1 ≤ t by omega)
      have hpos : 0 < s ^ 2 := pow_pos hs _
      omega
    have hellltp : ell < p := by
      rcases (hell.dvd_mul).mp hdiv with hdt | hdu
      · exact lt_of_le_of_lt (Nat.le_of_dvd ht hdt) htlp
      · exact lt_of_le_of_lt (Nat.le_of_dvd hu hdu) hulp
    have hellnots : ¬ell ∣ s := by
      intro hds
      have hellp : ell ∣ p := by
        rw [hrep, pow_two]
        exact dvd_add (hds.mul_right s) hdiv
      have heq : ell = p := (Nat.prime_dvd_prime_iff_eq hell hpp).mp hellp
      omega
    have hcop : s.Coprime ell := (hell.coprime_iff_not_dvd.mpr hellnots).symm
    have hcopZ : (s : ℤ).gcd ell = 1 := by
      simpa only [Int.gcd_natCast_natCast] using hcop.gcd_eq_one
    have hsq : jacobiSym ((s : ℤ) ^ 2) ell = 1 := jacobiSym.sq_one' hcopZ
    obtain ⟨w, hw⟩ := hdiv
    have hrepZ : (p : ℤ) = (s : ℤ) ^ 2 + (t : ℤ) * (u : ℤ) := by
      exact_mod_cast hrep
    have htwZ : (t : ℤ) * (u : ℤ) = (ell : ℤ) * (w : ℤ) := by
      exact_mod_cast hw
    have hmod : (p : ℤ) % (ell : ℤ) = ((s : ℤ) ^ 2) % ell := by
      calc
        (p : ℤ) % ell = ((s : ℤ) ^ 2 + (t : ℤ) * (u : ℤ)) % ell := by
          rw [hrepZ]
        _ = ((s : ℤ) ^ 2 + (ell : ℤ) * (w : ℤ)) % ell := by rw [htwZ]
        _ = ((s : ℤ) ^ 2) % ell := by simp [Int.add_emod]
    have hJp : jacobiSym (p : ℤ) ell = 1 :=
      (jacobiSym.mod_left' hmod).trans hsq
    have hp4 : p % 4 = 1 := by omega
    have hrec : jacobiSym (p : ℤ) ell = jacobiSym (ell : ℤ) p :=
      jacobiSym.quadratic_reciprocity_one_mod_four hp4 hellodd
    exact hrec.symm.trans hJp

/-- With `A=B+C`, the Eisenstein norm is `p=B²+A*C=C²+A*B`.
Every prime factor of *any* of the three unit-orbit axes `A,B,C=A-B`
is a residue modulo a hard prime `p`. -/
theorem eisenstein_axis_factors_residue (p A B C ell : ℕ)
    (hpp : p.Prime) (hp8 : p % 8 = 1) (hB : 0 < B) (hC : 0 < C)
    (hABC : A = B + C) (hrep : p = B ^ 2 + A * C)
    (hell : ell.Prime) (hdiv : ell ∣ A * B * C) :
    jacobiSym (ell : ℤ) p = 1 := by
  have hA : 0 < A := by omega
  have hrep2 : p = C ^ 2 + A * B := by
    rw [hrep, hABC]
    ring
  rcases (hell.dvd_mul).mp hdiv with hab | hc
  · exact square_plus_product_prime_factor_residue p C A B ell hpp hp8 hC hA
      hB hrep2 hell hab
  · have hac : ell ∣ A * C := by
      exact (hell.dvd_mul).mpr (Or.inr hc)
    exact square_plus_product_prime_factor_residue p B A C ell hpp hp8 hB hA
      hC hrep hell hac

/-- No first denominator supported entirely on the three Eisenstein axes
can satisfy *either full* divisor criterion (including cofactors dividing
`x²` but not `x`). This assumes `p < 4x` and `x < p`, not existence of x. -/
theorem eisenstein_supported_candidate_no_types (p A B C x e : ℕ)
    (hpp : p.Prime) (hp8 : p % 8 = 1) (hB : 0 < B) (hC : 0 < C)
    (hABC : A = B + C) (hrep : p = B ^ 2 + A * C)
    (hlo : p < 4 * x) (hhi : x < p) (hxdvd : x ∣ (A * B * C) ^ e) :
    ¬TypeI p x ∧ ¬TypeII p x := by
  apply no_types_if_prime_factors_residue p x hpp hp8 hlo hhi
  intro ell hell helld
  exact eisenstein_axis_factors_residue p A B C ell hpp hp8 hB hC hABC hrep
    hell (hell.dvd_of_dvd_pow (dvd_trans helld hxdvd))

/-- Combining Gaussian and Eisenstein coordinates does NOT improve the
prime-factor sieve: their whole product still has only residue factors. -/
theorem paired_norm_supported_candidate_no_types (p u v A B C x e : ℕ)
    (hpp : p.Prime) (hp8 : p % 8 = 1)
    (hu : 0 < u) (hv : 0 < v) (hGrep : p = u ^ 2 + v ^ 2)
    (hB : 0 < B) (hC : 0 < C) (hABC : A = B + C)
    (hErep : p = B ^ 2 + A * C)
    (hlo : p < 4 * x) (hhi : x < p)
    (hxdvd : x ∣ (u * v * (A * B * C)) ^ e) :
    ¬TypeI p x ∧ ¬TypeII p x := by
  apply no_types_if_prime_factors_residue p x hpp hp8 hlo hhi
  intro ell hell helld
  have hbase : ell ∣ u * v * (A * B * C) :=
    hell.dvd_of_dvd_pow (dvd_trans helld hxdvd)
  rcases (hell.dvd_mul).mp hbase with hG | hE
  · exact gaussian_coordinate_factors_residue p u v ell hpp hp8 hu hv hGrep
      hell hG
  · exact eisenstein_axis_factors_residue p A B C ell hpp hp8 hB hC hABC
      hErep hell hE

/-- Even if both norm representations are known, an actual Type-I or
Type-II solution must introduce a nonresidue prime not dividing *any*
Gaussian or Eisenstein axis. This is necessary, not sufficient. -/
theorem hard_paired_norm_solution_needs_external_prime (k u v A B C x : ℕ)
    (hpp : (24 * k + 1).Prime)
    (hu : 0 < u) (hv : 0 < v) (hGrep : 24 * k + 1 = u ^ 2 + v ^ 2)
    (hB : 0 < B) (hC : 0 < C) (hABC : A = B + C)
    (hErep : 24 * k + 1 = B ^ 2 + A * C)
    (hlo : 24 * k + 1 < 4 * x) (hhi : x < 24 * k + 1)
    (hw : TypeI (24 * k + 1) x ∨ TypeII (24 * k + 1) x) :
    ∃ ell : ℕ, ell.Prime ∧ 5 ≤ ell ∧ ell ∣ x ∧
      ¬ell ∣ u * v * (A * B * C) ∧
      jacobiSym (ell : ℤ) (24 * k + 1) = -1 := by
  obtain ⟨ell, hell, h5, helld, hneg⟩ :=
    hard_types_need_large_nonresidue k x hpp hlo hhi hw
  refine ⟨ell, hell, h5, helld, ?_, hneg⟩
  intro hbase
  have hpos : jacobiSym (ell : ℤ) (24 * k + 1) = 1 := by
    rcases (hell.dvd_mul).mp hbase with hG | hE
    · exact gaussian_coordinate_factors_residue (24 * k + 1) u v ell hpp
        (by omega) hu hv hGrep hell hG
    · exact eisenstein_axis_factors_residue (24 * k + 1) A B C ell hpp
        (by omega) hB hC hABC hErep hell hE
  omega

/-- At all three requested primes there are eligible Eisenstein-axis
products, none of which can satisfy either *complete* Type I or Type II. -/
theorem eisenstein_axis_product_193_fails :
    ¬TypeI 193 63 ∧ ¬TypeII 193 63 := by
  apply eisenstein_supported_candidate_no_types 193 16 9 7 63 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eisenstein_axis_product_2521_fails :
    ¬TypeI 2521 840 ∧ ¬TypeII 2521 840 := by
  apply eisenstein_supported_candidate_no_types 2521 56 41 15 840 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem eisenstein_axis_product_6553_fails :
    ¬TypeI 6553 1728 ∧ ¬TypeII 6553 1728 := by
  apply eisenstein_supported_candidate_no_types 6553 91 64 27 1728 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- A 7-norm twisted Eisenstein coordinate (`|2A-3B|=5,11,10`)
leads to *actual* witnesses at these three primes, but not universally. -/
theorem eisenstein_twist_193_typeI : TypeI 193 50 := by
  refine ⟨5, by norm_num, by norm_num, by norm_num⟩

theorem eisenstein_twist_2521_typeII : TypeII 2521 638 := by
  refine ⟨44, by norm_num, by norm_num, by norm_num, by norm_num⟩

theorem eisenstein_twist_2521_typeI : TypeI 2521 638 := by
  refine ⟨116, by norm_num, by norm_num, by norm_num⟩

theorem eisenstein_twist_6553_typeI : TypeI 6553 1640 := by
  refine ⟨5, by norm_num, by norm_num, by norm_num⟩

theorem eisenstein_twist_6553_typeII : TypeII 6553 1640 := by
  refine ⟨5, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- In each stress test, the displayed twisted-coordinate witness yields
*strictly ordered* positive unit fractions, not just a local congruence. -/
theorem eisenstein_twist_193_good : Good 193 :=
  good_of_typeI 193 50 (by norm_num) (by norm_num) (by norm_num)
    eisenstein_twist_193_typeI

theorem eisenstein_twist_2521_good : Good 2521 :=
  good_of_typeII 2521 638 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) eisenstein_twist_2521_typeII

theorem eisenstein_twist_6553_good : Good 6553 :=
  good_of_typeI 6553 1640 (by norm_num) (by norm_num) (by norm_num)
    eisenstein_twist_6553_typeI

theorem eisenstein_twist_6553_explicit :
    (4 / 6553 : ℚ) = 1 / 1640 + 1 / 1612120 + 1 / 32207995 := by
  norm_num

end Erdos242
