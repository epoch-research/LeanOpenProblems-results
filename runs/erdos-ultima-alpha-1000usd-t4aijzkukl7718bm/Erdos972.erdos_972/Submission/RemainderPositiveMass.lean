import Submission.RemainderRoughSupport
import Submission.PrimeIntervalCounts

/-! Structured positive values of the actual Vaughan remainder. -/
namespace Erdos972RemainderPositiveMass

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta Pointwise
open Erdos972Vaughan Erdos972DoubleVaughan Erdos972VaughanRemainderSigns

set_option maxHeartbeats 1000000

lemma divisors_two_primes {p q : ℕ} (hp : p.Prime) (hq : q.Prime) :
    (p*q).divisors = {1,p,q,p*q} := by
  rw [Nat.divisors_mul, hp.divisors, hq.divisors]
  ext d
  simp only [mem_mul, mem_insert, mem_singleton]
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨1, Or.inl rfl, 1, Or.inl rfl, by simp⟩
    · exact ⟨d, Or.inr rfl, 1, Or.inl rfl, by simp⟩
    · exact ⟨1, Or.inl rfl, d, Or.inr rfl, by simp⟩
    · exact ⟨p, Or.inr rfl, q, Or.inr rfl, rfl⟩

lemma divisors_three_primes {r s q : ℕ} (hr : r.Prime) (hs : s.Prime) (hq : q.Prime) :
    (r*s*q).divisors = {1,r,s,r*s,q,r*q,s*q,r*s*q} := by
  rw [Nat.divisors_mul, divisors_two_primes hr hs, hq.divisors]
  ext d
  simp only [mem_mul, mem_insert, mem_singleton]
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl <;> simp
  · rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    · exact ⟨1, Or.inl rfl, 1, Or.inl rfl, by simp⟩
    · exact ⟨d, Or.inr (Or.inl rfl), 1, Or.inl rfl, by simp⟩
    · exact ⟨d, Or.inr (Or.inr (Or.inl rfl)), 1, Or.inl rfl, by simp⟩
    · exact ⟨r*s, Or.inr (Or.inr (Or.inr rfl)), 1, Or.inl rfl, by simp⟩
    · exact ⟨1, Or.inl rfl, d, Or.inr rfl, by simp⟩
    · exact ⟨r, Or.inr (Or.inl rfl), q, Or.inr rfl, rfl⟩
    · exact ⟨s, Or.inr (Or.inr (Or.inl rfl)), q, Or.inr rfl, rfl⟩
    · exact ⟨r*s, Or.inr (Or.inr (Or.inr rfl)), q, Or.inr rfl, rfl⟩

lemma tail_moebius_semiprime {r s W : ℕ} (hr : r.Prime) (hs : s.Prime)
    (hrs : r ≠ s) (hrW : r ≤ W) (hsW : s ≤ W) (hW : W < r*s) :
    (tail (μ : ArithmeticFunction ℝ) W*ζ) (r*s) = 1 := by
  have hc : r.Coprime s := (Nat.coprime_primes hr hs).mpr hrs
  have hμ : (μ (r*s) : ℝ) = 1 := by
    rw [isMultiplicative_moebius.map_mul_of_coprime hc,
      moebius_apply_prime hr, moebius_apply_prime hs]
    norm_num
  rw [ArithmeticFunction.coe_mul_zeta_apply, divisors_two_primes hr hs,
    sum_eq_single (r*s)]
  · rw [tail_eq_of_lt _ hW, ArithmeticFunction.intCoe_apply, hμ]
  · intro d hd hdne
    simp only [mem_insert, mem_singleton] at hd
    rcases hd with rfl | rfl | rfl | he
    · exact tail_eq_zero_of_le _ (hr.one_le.trans hrW)
    · exact tail_eq_zero_of_le _ hrW
    · exact tail_eq_zero_of_le _ hsW
    · exact (hdne he).elim
  · simp

/-- Positive logarithmic values occur on a structured family of nonrough
integers, not merely on one isolated numerical example. -/
theorem typeIIPart_three_primes {r s q W : ℕ} (hr : r.Prime) (hs : s.Prime)
    (hq : q.Prime) (hrs : r ≠ s) (hrW : r ≤ W) (hsW : s ≤ W)
    (hWrs : W < r*s) (hWq : W < q) :
    typeIIPart W W (r*s*q) = Real.log q := by
  have hrq : r ≠ q := ne_of_lt (hrW.trans_lt hWq)
  have hsq : s ≠ q := ne_of_lt (hsW.trans_lt hWq)
  have hΛrs : vonMangoldt (r*s) = 0 :=
    mangoldt_zero_two_primes hr hs hrs (dvd_mul_right _ _) (dvd_mul_left _ _)
  have hΛrq : vonMangoldt (r*q) = 0 :=
    mangoldt_zero_two_primes hr hq hrq (dvd_mul_right _ _) (dvd_mul_left _ _)
  have hΛsq : vonMangoldt (s*q) = 0 :=
    mangoldt_zero_two_primes hs hq hsq (dvd_mul_right _ _) (dvd_mul_left _ _)
  have hΛn : vonMangoldt (r*s*q) = 0 :=
    mangoldt_zero_two_primes hr hs hrs
      ((dvd_mul_right r s).trans (dvd_mul_right (r*s) q))
      ((dvd_mul_left s r).trans (dvd_mul_right (r*s) q))
  unfold typeIIPart
  rw [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal'
    (fun a b => (tail (μ : ArithmeticFunction ℝ) W*ζ) a*tail Λ W b),
    divisors_three_primes hr hs hq, sum_eq_single q]
  · rw [Nat.mul_div_cancel _ hq.pos, tail_moebius_semiprime hr hs hrs hrW hsW hWrs,
      tail_eq_of_lt _ hWq, vonMangoldt_apply_prime hq, one_mul]
  · intro d hd hdq
    have hzero : tail Λ W d = 0 := by
      simp only [mem_insert, mem_singleton] at hd
      rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · simp [tail, Erdos972Vaughan.sub_apply, cutoff_apply]
      · exact tail_eq_zero_of_le _ hrW
      · exact tail_eq_zero_of_le _ hsW
      · simp [tail, Erdos972Vaughan.sub_apply, cutoff_apply, hΛrs]
      · exact (hdq rfl).elim
      · simp [tail, Erdos972Vaughan.sub_apply, cutoff_apply, hΛrq]
      · simp [tail, Erdos972Vaughan.sub_apply, cutoff_apply, hΛsq]
      · simp [tail, Erdos972Vaughan.sub_apply, cutoff_apply, hΛn]
    rw [hzero, mul_zero]
  · simp

#print axioms typeIIPart_three_primes

end Erdos972RemainderPositiveMass
