import Submission.TypeIPolynomial
import Submission.VaughanRemainderSigns
import Submission.LogarithmicCovariance

/-! Exact rough-semiprime values and a two-cluster lower bound for the
variance of the genuine Vaughan remainder. -/
namespace Erdos972RemainderSemiprimes

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta
open Erdos972Vaughan Erdos972DoubleVaughan Erdos972TypeIPolynomial
open Erdos972VaughanRemainderSigns Erdos972LogarithmicCovariance

set_option maxHeartbeats 1000000

lemma small_divisor_semiprime {p q U d : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hUp : U < p) (hUq : U < q) (hd : d ∣ p*q) (hdU : d ≤ U) : d = 1 := by
  by_contra hd1
  obtain ⟨r, hr, hrd⟩ := Nat.ne_one_iff_exists_prime_dvd.mp hd1
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hd (Nat.mul_pos hp.pos hq.pos)
  have hrU : r ≤ U := (Nat.le_of_dvd hdpos hrd).trans hdU
  rcases hr.dvd_mul.mp (hrd.trans hd) with hrp | hrq
  · have he : r = p := (Nat.dvd_prime hp).mp hrp |>.resolve_left hr.ne_one
    omega
  · have he : r = q := (Nat.dvd_prime hq).mp hrq |>.resolve_left hr.ne_one
    omega

lemma cutoff_mangoldt_semiprime_divisor {p q V d : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hVp : V < p) (hVq : V < q) (hd : d ∣ p*q) : cutoff Λ V d = 0 := by
  by_cases hdV : d ≤ V
  · have he := small_divisor_semiprime hp hq hVp hVq hd hdV
    rw [he, cutoff_apply, vonMangoldt_apply_one]
    split_ifs <;> rfl
  · exact cutoff_eq_zero_of_lt _ (Nat.lt_of_not_ge hdV)

lemma typeIPart_rough_semiprime {p q U V : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hU : 0 < U) (hUp : U < p) (hUq : U < q) (hVp : V < p) (hVq : V < q) :
    typeIPart U V (p*q) = Real.log (p*q : ℕ) := by
  have hn : 0 < p*q := Nat.mul_pos hp.pos hq.pos
  have hfirst : (cutoff (μ : ArithmeticFunction ℝ) U*ArithmeticFunction.log) (p*q) = Real.log (p*q : ℕ) := by
    rw [first_log_divisor_sum U hn, sum_eq_single 1]
    · simp [slopeCoeff, cutoff_eq_of_le _ hU]
    · intro d hd hd1
      have hdU : U < d := by
        by_contra hh
        exact hd1 (small_divisor_semiprime hp hq hUp hUq (Nat.mem_divisors.mp hd).1 (Nat.le_of_not_gt hh))
      rw [slopeCoeff, cutoff_eq_zero_of_lt _ hdU, zero_mul]
    · intro hh
      exact (hh (Nat.mem_divisors.mpr ⟨one_dvd _, Nat.ne_of_gt hn⟩)).elim
  have hsecond : (cutoff (μ : ArithmeticFunction ℝ) U*ζ*cutoff Λ V) (p*q) = 0 := by
    rw [ArithmeticFunction.mul_apply]
    apply sum_eq_zero
    intro ab hab
    have he := (Nat.mem_divisorsAntidiagonal.mp hab).1
    have hb : ab.2 ∣ p*q := he ▸ dvd_mul_left ab.2 ab.1
    rw [cutoff_mangoldt_semiprime_divisor hp hq hVp hVq hb, mul_zero]
  simp only [typeIPart, ArithmeticFunction.add_apply, Erdos972Vaughan.sub_apply, hfirst, hsecond,
    cutoff_mangoldt_semiprime_divisor hp hq hVp hVq (dvd_refl (p*q)), sub_zero, add_zero]

/-- At a product of two distinct primes above both cutoffs, the remainder
is minus the full logarithm, rather than a small error. -/
theorem typeIIPart_rough_semiprime {p q U V : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hU : 0 < U) (hUp : U < p) (hUq : U < q) (hVp : V < p) (hVq : V < q) :
    typeIIPart U V (p*q) = -Real.log (p*q : ℕ) := by
  have hh := congrArg (fun f : ArithmeticFunction ℝ => f (p*q)) (mangoldt_split U V)
  simp only [ArithmeticFunction.add_apply] at hh
  rw [typeIPart_rough_semiprime hp hq hU hUp hUq hVp hVq,
    mangoldt_zero_two_primes hp hq hpq (dvd_mul_right p q) (dvd_mul_left q p)] at hh
  linarith only [hh]

/-- Two separated value clusters force variance, irrespective of the actual
mean. This avoids estimating the mean of the signed remainder. -/
theorem covariance_self_two_clusters {N : ℕ} (hN : 0 < N) (f : ℕ → ℝ) (P S : Finset ℕ)
    (hPN : P ⊆ Ioc 0 N) (hSN : S ⊆ Ioc 0 N) {L m : ℝ} (hL : 0 ≤ L) (hm : 0 ≤ m)
    (hPcard : m ≤ P.card) (hScard : m ≤ S.card)
    (hP : ∀ n ∈ P, f n = 0) (hS : ∀ n ∈ S, f n ≤ -L) :
    m*L^2/4 ≤ covariance N f f := by
  rw [covariance_self_eq_squares hN]
  let c := total N f/N
  rw [mul_div_assoc]
  by_cases hc : c ≤ -L/2
  · have hpoint : ∀ n ∈ P, L^2/4 ≤ (f n-c)^2 := by
      intro n hn
      rw [hP n hn]
      nlinarith only [hc, hL, sq_nonneg (c+L/2)]
    calc
      _ ≤ (P.card : ℝ)*(L^2/4) := mul_le_mul_of_nonneg_right hPcard (by positivity)
      _ = ∑ n ∈ P, L^2/4 := by simp
      _ ≤ ∑ n ∈ P, (f n-c)^2 := sum_le_sum hpoint
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg hPN (fun _ _ _ => sq_nonneg _)
  · have hpoint : ∀ n ∈ S, L^2/4 ≤ (f n-c)^2 := by
      intro n hn
      have hh := hS n hn
      have hdist : f n-c ≤ -L/2 := by linarith only [hh, hc]
      nlinarith only [hdist, hL, sq_nonneg (f n-c+L/2)]
    calc
      _ ≤ (S.card : ℝ)*(L^2/4) := mul_le_mul_of_nonneg_right hScard (by positivity)
      _ = ∑ n ∈ S, L^2/4 := by simp
      _ ≤ ∑ n ∈ S, (f n-c)^2 := sum_le_sum hpoint
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg hSN (fun _ _ _ => sq_nonneg _)

#print axioms typeIIPart_rough_semiprime
#print axioms covariance_self_two_clusters

end Erdos972RemainderSemiprimes
