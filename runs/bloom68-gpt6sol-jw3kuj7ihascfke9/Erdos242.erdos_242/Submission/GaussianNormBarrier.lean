import Submission.PointwiseJacobi
import Mathlib.NumberTheory.SumTwoSquares

/-!
# Gaussian norm coordinates and the pointwise Jacobi obstruction

At a prime `p ≡ 1 (mod 8)` represented by `p = u² + v²`, every prime
factor of either Gaussian coordinate `u` or `v` is a quadratic residue
modulo `p`. Thus using only coordinate factors for an eligible first
denominator cannot satisfy *either* of the full divisor criteria.

This is an obstruction to a particular norm-based construction, NOT a
counterexample or a proof of the Erdős–Straus conjecture. `Spec.lean` is
neither imported nor edited.
-/

namespace Erdos242

/-- Quadratic reciprocity shows that a prime factor of one Gaussian
coordinate is a residue modulo the norm prime. The odd case uses
`p ≡ s² (mod ell)`; the prime `2` uses `p ≡ 1 (mod 8)`. -/
private theorem gaussian_coordinate_prime_residue (p t s ell : ℕ)
    (hpp : p.Prime) (hp8 : p % 8 = 1) (ht : 0 < t) (hs : 0 < s)
    (hrep : p = t ^ 2 + s ^ 2) (hell : ell.Prime) (helld : ell ∣ t) :
    jacobiSym (ell : ℤ) p = 1 := by
  rcases hell.eq_two_or_odd' with htwo | hellodd
  · subst ell
    have hpodd : Odd p := Nat.odd_iff.mpr (by omega)
    change jacobiSym (2 : ℤ) p = 1
    rw [jacobiSym.at_two hpodd, ZMod.χ₈_nat_eq_if_mod_eight]
    have hp2 : p % 2 = 1 := by omega
    simp [hp2, hp8]
  · have htlt : t < p := by
      rw [hrep]
      nlinarith
    have hellltp : ell < p := lt_of_le_of_lt (Nat.le_of_dvd ht helld) htlt
    have hellnots : ¬ell ∣ s := by
      intro hells
      have hellp : ell ∣ p := by
        rw [hrep, pow_two, pow_two]
        exact dvd_add (helld.mul_right t) (hells.mul_right s)
      have heq : ell = p := (Nat.prime_dvd_prime_iff_eq hell hpp).mp hellp
      omega
    have hcop : s.Coprime ell := (hell.coprime_iff_not_dvd.mpr hellnots).symm
    have hcopZ : (s : ℤ).gcd ell = 1 := by
      simpa only [Int.gcd_natCast_natCast] using hcop.gcd_eq_one
    have hsq : jacobiSym ((s : ℤ) ^ 2) ell = 1 := jacobiSym.sq_one' hcopZ
    obtain ⟨w, hw⟩ := helld
    have hrepZ : (p : ℤ) = (t : ℤ) ^ 2 + (s : ℤ) ^ 2 := by exact_mod_cast hrep
    have htwZ : (t : ℤ) = (ell : ℤ) * (w : ℤ) := by exact_mod_cast hw
    have hmod : (p : ℤ) % (ell : ℤ) = ((s : ℤ) ^ 2) % ell := by
      calc
        (p : ℤ) % ell = ((t : ℤ) ^ 2 + (s : ℤ) ^ 2) % ell := by rw [hrepZ]
        _ = ((ell : ℤ) * ((ell : ℤ) * (w : ℤ) ^ 2) + (s : ℤ) ^ 2) % ell := by
          rw [htwZ]
          ring_nf
        _ = ((s : ℤ) ^ 2) % ell := by simp [Int.add_emod]
    have hJp : jacobiSym (p : ℤ) ell = 1 :=
      (jacobiSym.mod_left' hmod).trans hsq
    have hp4 : p % 4 = 1 := by omega
    have hrec : jacobiSym (p : ℤ) ell = jacobiSym (ell : ℤ) p :=
      jacobiSym.quadratic_reciprocity_one_mod_four hp4 hellodd
    exact hrec.symm.trans hJp

/-- **Both** coordinates of a sum-of-two-squares prime have only
quadratic-residue prime factors (including `2` for `p ≡ 1 (mod 8)`). -/
theorem gaussian_coordinate_factors_residue (p u v ell : ℕ)
    (hpp : p.Prime) (hp8 : p % 8 = 1) (hu : 0 < u) (hv : 0 < v)
    (hrep : p = u ^ 2 + v ^ 2) (hell : ell.Prime) (hdiv : ell ∣ u * v) :
    jacobiSym (ell : ℤ) p = 1 := by
  rcases (hell.dvd_mul).mp hdiv with hdu | hdv
  · exact gaussian_coordinate_prime_residue p u v ell hpp hp8 hu hv hrep hell hdu
  · apply gaussian_coordinate_prime_residue p v u ell hpp hp8 hv hu
      (by nlinarith only [hrep]) hell hdv

/-- No eligible first denominator assembled exclusively from the Gaussian
coordinate prime factors can satisfy either **full** Type-I or Type-II
criterion. `x ∣ (u*v)^e` is a support condition, not a size bound. -/
theorem gaussian_supported_candidate_no_types (p u v x e : ℕ)
    (hpp : p.Prime) (hp8 : p % 8 = 1) (hu : 0 < u) (hv : 0 < v)
    (hrep : p = u ^ 2 + v ^ 2) (hlo : p < 4 * x) (hhi : x < p)
    (hxdvd : x ∣ (u * v) ^ e) :
    ¬TypeI p x ∧ ¬TypeII p x := by
  apply no_types_if_prime_factors_residue p x hpp hp8 hlo hhi
  intro ell hell helld
  have hpower : ell ∣ (u * v) ^ e := dvd_trans helld hxdvd
  exact gaussian_coordinate_factors_residue p u v ell hpp hp8 hu hv hrep hell
    (hell.dvd_of_dvd_pow hpower)

/-- In particular `x=u*v` is strictly below `p/2` and, whenever
`p<4uv`, is an eligible but **impossible** first denominator. -/
theorem gaussian_product_no_types (p u v : ℕ)
    (hpp : p.Prime) (hp8 : p % 8 = 1) (hrep : p = u ^ 2 + v ^ 2)
    (hlo : p < 4 * (u * v)) :
    ¬TypeI p (u * v) ∧ ¬TypeII p (u * v) := by
  have hu : 0 < u := by
    by_contra h
    have heq : u = 0 := by omega
    simp [heq] at hlo
  have hv : 0 < v := by
    by_contra h
    have heq : v = 0 := by omega
    simp [heq] at hlo
  have hAMZ : (2 : ℤ) * (u : ℤ) * v ≤ (u : ℤ) ^ 2 + (v : ℤ) ^ 2 := by
    nlinarith [sq_nonneg ((u : ℤ) - (v : ℤ))]
  have hAM : 2 * (u * v) ≤ u ^ 2 + v ^ 2 := by
    have hAM' : 2 * u * v ≤ u ^ 2 + v ^ 2 := by exact_mod_cast hAMZ
    simpa only [mul_assoc] using hAM'
  have hbelowhalf : 2 * (u * v) < p := by
    have hpge : 2 * (u * v) ≤ p := by rw [hrep]; exact hAM
    omega
  have hxltp : u * v < p := by omega
  apply gaussian_supported_candidate_no_types p u v (u * v) 1 hpp hp8 hu hv hrep
    hlo hxltp
  simp

/-- A solution for a hard prime MUST use a nonresidue prime factor of `x`
**outside both coordinates** of any Gaussian representation of `p`.
This is a necessary condition, not a construction of `x`. -/
theorem hard_gaussian_solution_needs_external_prime (k u v x : ℕ)
    (hpp : (24 * k + 1).Prime) (hu : 0 < u) (hv : 0 < v)
    (hrep : 24 * k + 1 = u ^ 2 + v ^ 2)
    (hlo : 24 * k + 1 < 4 * x) (hhi : x < 24 * k + 1)
    (hw : TypeI (24 * k + 1) x ∨ TypeII (24 * k + 1) x) :
    ∃ ell : ℕ, ell.Prime ∧ 5 ≤ ell ∧ ell ∣ x ∧ ¬ell ∣ u * v ∧
      jacobiSym (ell : ℤ) (24 * k + 1) = -1 := by
  obtain ⟨ell, hell, h5, helld, hneg⟩ :=
    hard_types_need_large_nonresidue k x hpp hlo hhi hw
  refine ⟨ell, hell, h5, helld, ?_, hneg⟩
  intro helluv
  have hpos : jacobiSym (ell : ℤ) (24 * k + 1) = 1 :=
    gaussian_coordinate_factors_residue (24 * k + 1) u v ell hpp (by omega)
      hu hv hrep hell helluv
  omega

/-- Fermat's two-squares theorem supplies the Gaussian representation
at **every** hard prime; this alone supplies no divisors in the required
Type-I or Type-II residue classes. -/
theorem hard_prime_has_gaussian_coordinates (k : ℕ) (hpp : (24 * k + 1).Prime) :
    ∃ u v : ℕ, 0 < u ∧ 0 < v ∧ 24 * k + 1 = u ^ 2 + v ^ 2 := by
  letI : Fact (24 * k + 1).Prime := ⟨hpp⟩
  obtain ⟨u, v, hrep⟩ := Nat.Prime.sq_add_sq (p := 24 * k + 1) (by omega)
  have hu : 0 < u := by
    by_contra hn
    have hu0 : u = 0 := by omega
    have hsquare : IsSquare (24 * k + 1) := by
      refine ⟨v, ?_⟩
      simpa [hu0, pow_two] using hrep.symm
    exact hpp.not_isSquare hsquare
  have hv : 0 < v := by
    by_contra hn
    have hv0 : v = 0 := by omega
    have hsquare : IsSquare (24 * k + 1) := by
      refine ⟨u, ?_⟩
      simpa [hv0, pow_two] using hrep.symm
    exact hpp.not_isSquare hsquare
  exact ⟨u, v, hu, hv, hrep.symm⟩

/-- An unconditional, pointwise consequence of Fermat's theorem for **every**
hard prime: one can choose positive Gaussian coordinates such that **every**
eligible first denominator supported on their prime factors misses both
complete divisor conditions. This does not exclude other first denominators. -/
theorem hard_prime_gaussian_supported_fibers_fail (k : ℕ)
    (hpp : (24 * k + 1).Prime) :
    ∃ u v : ℕ, 0 < u ∧ 0 < v ∧ 24 * k + 1 = u ^ 2 + v ^ 2 ∧
      ∀ x e : ℕ, 24 * k + 1 < 4 * x → x < 24 * k + 1 →
        x ∣ (u * v) ^ e → ¬TypeI (24 * k + 1) x ∧ ¬TypeII (24 * k + 1) x := by
  obtain ⟨u, v, hu, hv, hrep⟩ := hard_prime_has_gaussian_coordinates k hpp
  refine ⟨u, v, hu, hv, hrep, ?_⟩
  intro x e hlo hhi hxdvd
  exact gaussian_supported_candidate_no_types (24 * k + 1) u v x e hpp
    (by omega) hu hv hrep hlo hhi hxdvd


/-- Three hard primes with balanced Gaussian coordinates all have a
failed Gaussian-product fiber, yet each prime is soluble elsewhere. -/
theorem gaussian_product_193_fails : ¬TypeI 193 84 ∧ ¬TypeII 193 84 := by
  simpa only [show (7 : ℕ) * 12 = 84 by norm_num] using
    gaussian_product_no_types 193 7 12 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)

theorem gaussian_product_2521_fails : ¬TypeI 2521 1260 ∧ ¬TypeII 2521 1260 := by
  simpa only [show (35 : ℕ) * 36 = 1260 by norm_num] using
    gaussian_product_no_types 2521 35 36 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)

theorem gaussian_product_6553_fails : ¬TypeI 6553 2664 ∧ ¬TypeII 6553 2664 := by
  simpa only [show (37 : ℕ) * 72 = 2664 by norm_num] using
    gaussian_product_no_types 6553 37 72 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)

/-- The *first* candidate at `193` is `49=7²`: its only prime
factor is a residue modulo `193`, so both full criteria fail there. -/
theorem first_candidate_193_fails : ¬TypeI 193 49 ∧ ¬TypeII 193 49 := by
  apply no_types_if_prime_factors_residue 193 49
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  intro ell hell helld
  have hfac : (49 : ℕ) = 7 ^ 2 := by norm_num
  rw [hfac] at helld
  have h7 : ell ∣ 7 := hell.dvd_of_dvd_pow helld
  have heq : ell = 7 :=
    ((Nat.Prime.dvd_iff_eq (by norm_num : Nat.Prime 7) hell.ne_one).mp h7).symm
  subst ell
  norm_num

/-- The first candidate at `2521` is itself a quadratic-residue
prime `631`; failure here says nothing about later candidates. -/
theorem first_candidate_2521_fails : ¬TypeI 2521 631 ∧ ¬TypeII 2521 631 := by
  apply no_types_if_prime_factors_residue 2521 631
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  intro ell hell helld
  have heq : ell = 631 :=
    ((Nat.Prime.dvd_iff_eq (by norm_num : Nat.Prime 631) hell.ne_one).mp helld).symm
  subst ell
  norm_num

/-- At `p=193` the Gaussian product `x=84` fails, but a genuinely
external prime `5` supplies a Type-I certificate at `x=50`. -/
theorem norm_escape_193_typeI : TypeI 193 50 := by
  refine ⟨5, by norm_num, by norm_num, by norm_num⟩

theorem norm_escape_193_good : Good 193 :=
  good_of_typeI 193 50 (by norm_num) (by norm_num) (by norm_num)
    norm_escape_193_typeI

theorem norm_escape_193_explicit :
    (4 / 193 : ℚ) = 1 / 50 + 1 / 1450 + 1 / 27985 := by
  norm_num

/-- At `p=2521`, the outside nonresidue `53` divides `636` and the
Type-II cofactor `8` gives a strictly ordered identity. -/
theorem norm_escape_2521_typeII : TypeII 2521 636 := by
  refine ⟨8, by norm_num, by norm_num, by norm_num, by norm_num⟩

theorem norm_escape_2521_good : Good 2521 :=
  good_of_typeII 2521 636 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    norm_escape_2521_typeII

theorem norm_escape_2521_explicit :
    (4 / 2521 : ℚ) = 1 / 636 + 1 / 70588 + 1 / 5611746 := by
  norm_num

/-- The first candidate for `6553` has *both* kinds of witness with
cofactor/divisor `11`, external to the Gaussian coordinates `37,72`. -/
theorem test_6553_typeI : TypeI 6553 1639 := by
  refine ⟨11, by norm_num, by norm_num, by norm_num⟩


theorem test_6553_typeII : TypeII 6553 1639 := by
  refine ⟨11, by norm_num, by norm_num, by norm_num, by norm_num⟩

theorem test_6553_good : Good 6553 :=
  good_of_typeII 6553 1639 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    test_6553_typeII

theorem test_6553_explicit :
    (4 / 6553 : ℚ) = 1 / 1639 + 1 / 3604150 + 1 / 537018350 := by
  norm_num

end Erdos242
