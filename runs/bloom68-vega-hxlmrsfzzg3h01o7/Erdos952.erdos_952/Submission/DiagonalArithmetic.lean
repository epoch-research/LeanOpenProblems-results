import Submission.SmallBound

/-!
# Arithmetic for the diagonal Gaussian-prime bound

Gaussian primes outside norms 2, 5 and 13 have odd coordinate sum and avoid
four linear congruences. This file proves those facts by explicit Gaussian
quotients, without requiring separate primality proofs for the sieve factors.
-/

namespace Erdos952.DiagonalBound

/-- The Gaussian-prime norms excluded by the sieve. -/
def exceptions : Set GaussianInt := {z | z.norm = 2 ∨ z.norm = 5 ∨ z.norm = 13}

/-- A concrete finite box containing all the exceptions. -/
def exceptionBox : Finset GaussianInt :=
  ((Finset.Icc (-4 : ℤ) 4) ×ˢ (Finset.Icc (-4 : ℤ) 4)).image
    (fun p : ℤ × ℤ => (⟨p.1, p.2⟩ : GaussianInt))

/-- Bounded norm supplies explicit coordinate bounds and membership in the box. -/
theorem mem_exceptionBox_of_norm_le {z : GaussianInt} (hz : z.norm ≤ 13) :
    z ∈ exceptionBox := by
  have hn : z.re ^ 2 + z.im ^ 2 ≤ 13 := by
    simpa [Zsqrtd.norm, pow_two] using hz
  have hre : -4 ≤ z.re ∧ z.re ≤ 4 := by
    constructor <;> nlinarith [sq_nonneg z.im]
  have him : -4 ≤ z.im ∧ z.im ≤ 4 := by
    constructor <;> nlinarith [sq_nonneg z.re]
  apply Finset.mem_image.mpr
  refine ⟨(z.re, z.im), ?_, ?_⟩
  · exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr hre, Finset.mem_Icc.mpr him⟩
  · cases z
    rfl

/-- The exceptional norm levels form a finite set. -/
theorem finite_exceptions : exceptions.Finite := by
  apply exceptionBox.finite_toSet.subset
  intro z hz
  apply mem_exceptionBox_of_norm_le
  change z.norm = 2 ∨ z.norm = 5 ∨ z.norm = 13 at hz
  omega

/-- Any nonunit divisor of a Gaussian prime has the same norm as that prime. -/
theorem norm_eq_of_prime_dvd {p a : GaussianInt} (hp : Prime p)
    (ha : a.norm ≠ 1) (hdvd : a ∣ p) : p.norm = a.norm := by
  apply Zsqrtd.norm_eq_of_associated (by norm_num : (-1 : ℤ) ≤ 0)
  apply (hp.irreducible.dvd_iff.mp hdvd).resolve_left
  intro hunit
  exact ha ((Zsqrtd.norm_eq_one_iff' (by norm_num : (-1 : ℤ) ≤ 0) a).mpr hunit)

/-- An explicit quotient by `2 - i`. -/
theorem twoSubI_dvd_of_congruence {z : GaussianInt} (h : (5 : ℤ) ∣ z.re + 2 * z.im) :
    (⟨2, -1⟩ : GaussianInt) ∣ z := by
  obtain ⟨k, hk⟩ := h
  refine ⟨⟨2 * k - z.im, k⟩, ?_⟩
  apply Zsqrtd.ext <;> simp
  omega

/-- An explicit quotient by `2 + i`. -/
theorem twoAddI_dvd_of_congruence {z : GaussianInt} (h : (5 : ℤ) ∣ z.re - 2 * z.im) :
    (⟨2, 1⟩ : GaussianInt) ∣ z := by
  obtain ⟨k, hk⟩ := h
  refine ⟨⟨2 * k + z.im, -k⟩, ?_⟩
  apply Zsqrtd.ext <;> simp
  omega

/-- An explicit quotient by `3 + 2i`. -/
theorem threeAddTwoI_dvd_of_congruence {z : GaussianInt}
    (h : (13 : ℤ) ∣ z.re + 5 * z.im) : (⟨3, 2⟩ : GaussianInt) ∣ z := by
  obtain ⟨k, hk⟩ := h
  refine ⟨⟨3 * k - z.im, z.im - 2 * k⟩, ?_⟩
  apply Zsqrtd.ext <;> simp <;> omega

/-- An explicit quotient by `3 - 2i`. -/
theorem threeSubTwoI_dvd_of_congruence {z : GaussianInt}
    (h : (13 : ℤ) ∣ z.re - 5 * z.im) : (⟨3, -2⟩ : GaussianInt) ∣ z := by
  obtain ⟨k, hk⟩ := h
  refine ⟨⟨3 * k + z.im, z.im + 2 * k⟩, ?_⟩
  apply Zsqrtd.ext <;> simp <;> omega

/-- Nonexceptional Gaussian primes pass all four congruence tests. -/
theorem prime_congruences {p : GaussianInt} (hp : Prime p) (he : p ∉ exceptions) :
    (p.re + 2 * p.im) % 5 ≠ 0 ∧ (p.re - 2 * p.im) % 5 ≠ 0 ∧
    (p.re + 5 * p.im) % 13 ≠ 0 ∧ (p.re - 5 * p.im) % 13 ≠ 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h
    have hn := norm_eq_of_prime_dvd hp (a := ⟨2, -1⟩)
      (by norm_num [Zsqrtd.norm]) (twoSubI_dvd_of_congruence (Int.dvd_of_emod_eq_zero h))
    apply he
    exact Or.inr (Or.inl (by simpa [Zsqrtd.norm] using hn))
  · intro h
    have hn := norm_eq_of_prime_dvd hp (a := ⟨2, 1⟩)
      (by norm_num [Zsqrtd.norm]) (twoAddI_dvd_of_congruence (Int.dvd_of_emod_eq_zero h))
    apply he
    exact Or.inr (Or.inl (by simpa [Zsqrtd.norm] using hn))
  · intro h
    have hn := norm_eq_of_prime_dvd hp (a := ⟨3, 2⟩)
      (by norm_num [Zsqrtd.norm]) (threeAddTwoI_dvd_of_congruence (Int.dvd_of_emod_eq_zero h))
    apply he
    exact Or.inr (Or.inr (by simpa [Zsqrtd.norm] using hn))
  · intro h
    have hn := norm_eq_of_prime_dvd hp (a := ⟨3, -2⟩)
      (by norm_num [Zsqrtd.norm]) (threeSubTwoI_dvd_of_congruence (Int.dvd_of_emod_eq_zero h))
    apply he
    exact Or.inr (Or.inr (by simpa [Zsqrtd.norm] using hn))

/-- Nonexceptional Gaussian primes have odd coordinate sum. -/
theorem prime_odd {p : GaussianInt} (hp : Prime p) (he : p ∉ exceptions) :
    Odd (p.re + p.im) := by
  apply SmallBound.odd_re_add_im_of_prime_not_mem hp
  intro h
  exact he (Or.inl (SmallBound.mem_evenPrimeExceptions_iff.mp h))

/-- The difference of two odd-parity Gaussian integers has even coordinate sum. -/
theorem even_sub_of_odd {p q : GaussianInt}
    (hp : Odd (p.re + p.im)) (hq : Odd (q.re + q.im)) :
    Even ((q - p).re + (q - p).im) := by
  have hsum : (q - p).re + (q - p).im = (q.re + q.im) - (p.re + p.im) := by
    simp only [Zsqrtd.re_sub, Zsqrtd.im_sub]
    ring
  rw [hsum]
  exact hq.sub_odd hp

/-- At squared norm below four, an even-parity displacement is zero or one of
exactly the four diagonal steps. In particular, no norm-three case is omitted. -/
theorem zero_or_diagonal_of_even_of_norm_lt_four {z : GaussianInt}
    (he : Even (z.re + z.im)) (hz : z.norm < 4) :
    z = 0 ∨ z = ⟨1, 1⟩ ∨ z = ⟨1, -1⟩ ∨ z = ⟨-1, 1⟩ ∨ z = ⟨-1, -1⟩ := by
  have hn : z.re ^ 2 + z.im ^ 2 < 4 := by
    simpa [Zsqrtd.norm, pow_two] using hz
  have hre : -1 ≤ z.re ∧ z.re ≤ 1 := by
    constructor <;> nlinarith [sq_nonneg z.im]
  have him : -1 ≤ z.im ∧ z.im ≤ 1 := by
    constructor <;> nlinarith [sq_nonneg z.re]
  obtain ⟨k, hk⟩ := he
  obtain ⟨hrl, hru⟩ := hre
  obtain ⟨hil, hiu⟩ := him
  interval_cases hr : z.re <;> interval_cases hi : z.im <;>
    simp_all [Zsqrtd.ext_iff] <;> omega

/-- Three is not the norm of any Gaussian integer. -/
theorem norm_ne_three (z : GaussianInt) : z.norm ≠ 3 := by
  intro hz
  have hn : z.re ^ 2 + z.im ^ 2 = 3 := by
    simpa [Zsqrtd.norm, pow_two] using hz
  have hre : -1 ≤ z.re ∧ z.re ≤ 1 := by
    constructor <;> nlinarith [sq_nonneg z.im]
  have him : -1 ≤ z.im ∧ z.im ≤ 1 := by
    constructor <;> nlinarith [sq_nonneg z.re]
  obtain ⟨hrl, hru⟩ := hre
  obtain ⟨hil, hiu⟩ := him
  interval_cases hr : z.re <;> interval_cases hi : z.im <;>
    norm_num [hr, hi] at hn

end Erdos952.DiagonalBound
