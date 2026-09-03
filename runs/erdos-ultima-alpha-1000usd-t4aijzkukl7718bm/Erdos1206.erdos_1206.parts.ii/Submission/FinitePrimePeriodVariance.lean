import Submission.FullPrimeScoreVariance

/-! Exact cancellation of distinct-prime covariance over a complete period. -/
namespace Erdos1206.FinitePrimePeriodVariance
open Finset PrimeBlockVariance SharpPrimeBlockVariance
open scoped Classical

lemma covariance_zero {D p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (hcop : Nat.Coprime p q) (hpD : p ∣ D) (hqD : q ∣ D) : covariance D p q=0 := by
  have hpqD : p*q ∣ D := hcop.mul_dvd_of_dvd_of_dvd hpD hqD
  rw [covariance_distinct hcop,Nat.cast_div hpqD,Nat.cast_div hpD,Nat.cast_div hqD]
  · push_cast
    ring
  all_goals positivity

/-- Arbitrary real weights are allowed. The period may contain extra factors. -/
theorem variance_le_period (D : ℕ) (P : Finset ℕ) (w : ℕ → ℝ)
    (hP : ∀ p ∈ P,p.Prime) (hD : ∀ p ∈ P,p ∣ D) :
    variance D P w ≤ (D:ℝ)*mass P w := by
  rw [variance_expand]
  have he (p : ℕ) (hp : p ∈ P) (q : ℕ) (hq : q ∈ P) :
      w p*w q*covariance D p q ≤ if p=q then (D:ℝ)*w p^2/p else 0 := by
    by_cases hpq : p=q
    · subst q
      rw [if_pos rfl]
      have hh := mul_le_mul_of_nonneg_left (covariance_self_le (hP p hp).two_le D) (sq_nonneg (w p))
      convert hh using 1 <;> ring
    · rw [if_neg hpq,covariance_zero (hP p hp).pos (hP q hq).pos
        ((Nat.coprime_primes (hP p hp) (hP q hq)).mpr hpq) (hD p hp) (hD q hq),mul_zero]
  calc
    _ ≤ ∑p∈P,∑q∈P,if p=q then (D:ℝ)*w p^2/p else 0 :=
      sum_le_sum (fun p hp => sum_le_sum (fun q hq => he p hp q hq))
    _ = _ := by
      have hi (p : ℕ) (hp : p ∈ P) : (∑q∈P,if p=q then (D:ℝ)*w p^2/p else 0)=(D:ℝ)*w p^2/p := by simp [hp]
      rw [sum_congr rfl hi]
      simp only [mass,mul_sum]
      apply sum_congr rfl
      intro p _
      ring

lemma primeSum_mod (P : Finset ℕ) (w : ℕ → ℝ) (D n : ℕ)
    (hD : ∀ p ∈ P,p ∣ D) : primeSum P w (n%D)=primeSum P w n := by
  apply sum_congr rfl
  intro p hp
  simp only [indicator,Nat.dvd_mod_iff (hD p hp)]

#print axioms variance_le_period
#print axioms primeSum_mod
end Erdos1206.FinitePrimePeriodVariance
