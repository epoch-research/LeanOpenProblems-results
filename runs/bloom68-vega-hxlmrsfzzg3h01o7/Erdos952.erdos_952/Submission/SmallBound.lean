import FormalConjecturesUtil
import Submission.FinitePotential

/-!
# A small unconditional bound for Gaussian-prime walks

There is no injective sequence of Gaussian primes whose squared step norms are
all `< C` for an integer `C ≤ 2`. Outside the four associates of `1 + i`, a
Gaussian prime has odd real-plus-imaginary part. The difference of two such
primes is divisible by `1 + i`, so its norm is either zero or at least two.
An injective sequence eventually avoids the four exceptions.

This is only a small-bound obstruction, not a solution of the Gaussian moat
problem. This file does not import `Submission.Spec`.
-/

namespace Erdos952
namespace SmallBound

/-- The Gaussian integer `1 + i`. -/
def oneAddI : GaussianInt := ⟨1, 1⟩

@[simp]
theorem norm_oneAddI : oneAddI.norm = 2 := by
  norm_num [oneAddI, Zsqrtd.norm]

/-- Divisibility by `1 + i` is exactly evenness of the sum of the coordinates.
For the reverse direction, if `re + im = k + k`, the quotient is
`⟨k, im - k⟩`. -/
theorem oneAddI_dvd_iff_even (z : GaussianInt) :
    oneAddI ∣ z ↔ Even (z.re + z.im) := by
  constructor
  · rintro ⟨w, rfl⟩
    refine ⟨w.re, ?_⟩
    simp [oneAddI, Zsqrtd.re_mul, Zsqrtd.im_mul]
    ring
  · rintro ⟨k, hk⟩
    refine ⟨⟨k, z.im - k⟩, ?_⟩
    apply Zsqrtd.ext
    · simp [oneAddI]
      omega
    · simp [oneAddI]

theorem not_isUnit_oneAddI : ¬ IsUnit oneAddI := by
  intro h
  have hn := (Zsqrtd.norm_eq_one_iff' (by norm_num : (-1 : ℤ) ≤ 0) oneAddI).mpr h
  simp at hn

/-- A Gaussian prime divisible by `1 + i` is associated to it. -/
theorem associated_oneAddI_of_prime_dvd {p : GaussianInt} (hp : Prime p)
    (hdvd : oneAddI ∣ p) : Associated p oneAddI := by
  exact (hp.irreducible.dvd_iff.mp hdvd).resolve_left not_isUnit_oneAddI

/-- The explicit four-element exceptional set. -/
def evenPrimeExceptions : Finset GaussianInt :=
  {⟨1, 1⟩, ⟨1, -1⟩, ⟨-1, 1⟩, ⟨-1, -1⟩}

@[simp]
theorem card_evenPrimeExceptions : evenPrimeExceptions.card = 4 := by
  decide

/-- Norm two characterizes the four exceptional points. -/
theorem mem_evenPrimeExceptions_iff {z : GaussianInt} :
    z ∈ evenPrimeExceptions ↔ z.norm = 2 := by
  constructor
  · intro hz
    simp only [evenPrimeExceptions, Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl | rfl <;> norm_num [Zsqrtd.norm]
  · intro hz
    have hn : z.re ^ 2 + z.im ^ 2 = 2 := by
      simpa [Zsqrtd.norm, pow_two] using hz
    have hre : -1 ≤ z.re ∧ z.re ≤ 1 := by
      constructor <;> nlinarith [sq_nonneg z.im]
    have him : -1 ≤ z.im ∧ z.im ≤ 1 := by
      constructor <;> nlinarith [sq_nonneg z.re]
    obtain ⟨hrl, hru⟩ := hre
    obtain ⟨hil, hiu⟩ := him
    interval_cases hr : z.re <;> interval_cases hi : z.im <;>
      norm_num [hr, hi] at hn <;>
      simp [hr, hi, evenPrimeExceptions, Zsqrtd.ext_iff]

/-- Every even-parity Gaussian prime lies in the explicit exceptional set. -/
theorem mem_evenPrimeExceptions_of_prime_even {p : GaussianInt} (hp : Prime p)
    (heven : Even (p.re + p.im)) : p ∈ evenPrimeExceptions := by
  apply mem_evenPrimeExceptions_iff.mpr
  have hassoc := associated_oneAddI_of_prime_dvd hp ((oneAddI_dvd_iff_even p).mpr heven)
  simpa using Zsqrtd.norm_eq_of_associated (by norm_num : (-1 : ℤ) ≤ 0) hassoc

/-- Thus the even-parity Gaussian primes form a finite set. -/
theorem finite_even_primes :
    {p : GaussianInt | Prime p ∧ Even (p.re + p.im)}.Finite := by
  apply evenPrimeExceptions.finite_toSet.subset
  intro p hp
  exact mem_evenPrimeExceptions_of_prime_even hp.1 hp.2

/-- Every nonexceptional Gaussian prime has odd coordinate sum. -/
theorem odd_re_add_im_of_prime_not_mem {p : GaussianInt} (hp : Prime p)
    (hpe : p ∉ evenPrimeExceptions) : Odd (p.re + p.im) := by
  apply Int.not_even_iff_odd.mp
  exact fun heven => hpe (mem_evenPrimeExceptions_of_prime_even hp heven)

/-- Two points with odd coordinate sums cannot be distinct at squared distance
strictly less than two. -/
theorem eq_of_odd_of_norm_sub_lt_two {p q : GaussianInt}
    (hp : Odd (p.re + p.im)) (hq : Odd (q.re + q.im))
    (hstep : (q - p).norm < 2) : q = p := by
  have heven : Even ((q - p).re + (q - p).im) := by
    have hsum : (q - p).re + (q - p).im = (q.re + q.im) - (p.re + p.im) := by
      simp only [Zsqrtd.re_sub, Zsqrtd.im_sub]
      ring
    rw [hsum]
    exact hq.sub_odd hp
  obtain ⟨w, hw⟩ := (oneAddI_dvd_iff_even (q - p)).mpr heven
  have hn : (q - p).norm = 2 * w.norm := by
    rw [hw, Zsqrtd.norm_mul, norm_oneAddI]
  have hw_nonneg := GaussianInt.norm_nonneg w
  have hw_zero : w.norm = 0 := by omega
  apply sub_eq_zero.mp
  rw [hw, GaussianInt.norm_eq_zero.mp hw_zero, mul_zero]

/-- Local obstruction outside the four exceptional Gaussian primes. -/
theorem eq_of_prime_not_mem_of_norm_sub_lt_two {p q : GaussianInt}
    (hp : Prime p) (hq : Prime q)
    (hpe : p ∉ evenPrimeExceptions) (hqe : q ∉ evenPrimeExceptions)
    (hstep : (q - p).norm < 2) : q = p := by
  exact eq_of_odd_of_norm_sub_lt_two
    (odd_re_add_im_of_prime_not_mem hp hpe)
    (odd_re_add_im_of_prime_not_mem hq hqe) hstep

end SmallBound

/-- Unconditional small-bound obstruction: no injective Gaussian-prime sequence
has every squared step norm `< C` when `C ≤ 2`. This does not address arbitrary
larger bounds in the Gaussian moat problem. -/
theorem no_bounded_step_sequence_of_bound_le_two {C : ℤ} (hC : C ≤ 2) :
    ¬ ∃ x : ℕ → GaussianInt, Function.Injective x ∧
      ∀ n, Prime (x n) ∧ (x (n + 1) - x n).norm < C := by
  rintro ⟨x, hx, hstep⟩
  obtain ⟨N, hN⟩ := FinitePotential.exists_tail_avoiding hx
    SmallBound.evenPrimeExceptions.finite_toSet
  have heq : x (N + 1) = x N := by
    apply SmallBound.eq_of_prime_not_mem_of_norm_sub_lt_two
      (hstep N).1 (hstep (N + 1)).1
    · simpa using hN 0
    · simpa using hN 1
    · exact lt_of_lt_of_le (hstep N).2 hC
  have hbad : N + 1 = N := hx heq
  omega

/-- Consequently any injective bounded-step Gaussian-prime sequence would need
an integral squared-norm bound of at least three. -/
theorem three_le_bound_of_witness {C : ℤ}
    (h : ∃ x : ℕ → GaussianInt, Function.Injective x ∧
      ∀ n, Prime (x n) ∧ (x (n + 1) - x n).norm < C) : 3 ≤ C := by
  by_contra hC
  exact no_bounded_step_sequence_of_bound_le_two (by omega) h

end Erdos952
