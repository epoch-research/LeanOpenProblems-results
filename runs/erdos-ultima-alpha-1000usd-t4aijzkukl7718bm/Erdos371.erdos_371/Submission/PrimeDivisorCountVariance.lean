import Submission.PrimeDivisorMoments

/-! Finite mean and variance bounds for the number of divisors in a chosen
prime set. All error terms come from exact counts of multiples. -/
namespace Erdos371.FiniteSieve
open Finset

def primeDivisorCountIn (S : Finset ℕ) (n : ℕ) : ℕ := (S.filter fun p => p ∣ n).card
noncomputable def primeReciprocalMass (S : Finset ℕ) : ℝ := ∑ p ∈ S, (1 : ℝ)/p

lemma primeReciprocalMass_nonneg (S : Finset ℕ) : 0 ≤ primeReciprocalMass S := by
  unfold primeReciprocalMass
  positivity

lemma primeDivisorCountIn_sum (S : Finset ℕ) (N : ℕ) :
    (∑ n ∈ range N, (primeDivisorCountIn S (n+1) : ℝ)) = ∑ p ∈ S, ((N/p : ℕ) : ℝ) := by
  have he (n : ℕ) : (primeDivisorCountIn S (n+1) : ℝ) =
      ∑ p ∈ S, if p ∣ n+1 then (1 : ℝ) else 0 := by simp [primeDivisorCountIn]
  simp_rw [he]
  rw [sum_comm]
  apply sum_congr rfl
  intro p hp
  simp [Nat.card_multiples]

lemma primeDivisorCountIn_mean_lower (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (N : ℕ) :
    (N : ℝ)*primeReciprocalMass S - S.card ≤
      ∑ n ∈ range N, (primeDivisorCountIn S (n+1) : ℝ) := by
  rw [primeDivisorCountIn_sum,primeReciprocalMass,mul_sum]
  have ht (p : ℕ) (hp : p ∈ S) : (N : ℝ)/p-1 ≤ ((N/p : ℕ) : ℝ) := by
    have h := Nat.lt_mul_div_succ N (hS p hp).pos
    have h' : (N : ℝ) ≤ (p : ℝ)*(((N/p : ℕ) : ℝ)+1) := by exact_mod_cast h.le
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (hS p hp).pos
    have hh := (div_le_iff₀ hp0).mpr (by nlinarith : (N : ℝ) ≤ (((N/p : ℕ) : ℝ)+1)*p)
    linarith
  have hh := sum_le_sum ht
  simpa only [sum_sub_distrib,sum_const,nsmul_eq_mul,mul_one,mul_one_div] using hh

lemma primeDivisorCountIn_second_moment (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (N : ℕ) :
    (∑ n ∈ range N, (primeDivisorCountIn S (n+1) : ℝ)^2) ≤
      N*((primeReciprocalMass S)^2+primeReciprocalMass S) := by
  simpa [primeDivisorCountIn,primeReciprocalMass] using
    prime_divisor_sum_sq_mean_le S hS (fun _ => (1 : ℝ)) (by intros; norm_num) N

/-- Variance about the reciprocal-prime mass, including the floor-count error. -/
theorem primeDivisorCountIn_variance_bound (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (N : ℕ) :
    (∑ n ∈ range N, ((primeDivisorCountIn S (n+1) : ℝ)-primeReciprocalMass S)^2) ≤
      N*primeReciprocalMass S+2*primeReciprocalMass S*S.card := by
  have hfirst := primeDivisorCountIn_mean_lower S hS N
  have hsecond := primeDivisorCountIn_second_moment S hS N
  have hA := primeReciprocalMass_nonneg S
  have he : (∑ n ∈ range N, ((primeDivisorCountIn S (n+1) : ℝ)-primeReciprocalMass S)^2) =
      (∑ n ∈ range N, (primeDivisorCountIn S (n+1) : ℝ)^2) -
        2*primeReciprocalMass S*(∑ n ∈ range N, (primeDivisorCountIn S (n+1) : ℝ)) +
          (N : ℝ)*(primeReciprocalMass S)^2 := by
    simp only [sub_sq,sum_add_distrib,sum_sub_distrib,← sum_mul,← mul_sum,
      sum_const,card_range,nsmul_eq_mul]
    ring
  rw [he]
  nlinarith [mul_le_mul_of_nonneg_left hfirst (by positivity : 0 ≤ 2*primeReciprocalMass S)]

/-- Chebyshev lower-tail bound: few integers have less than half the expected
number of prime divisors from S. -/
theorem primeDivisorCountIn_low_count_bound (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    (N : ℕ) (hN : 0 < N) (hA : 0 < primeReciprocalMass S) :
    (((range N).filter fun n => (primeDivisorCountIn S (n+1) : ℝ) ≤ primeReciprocalMass S/2).card : ℝ)/N ≤
      4/primeReciprocalMass S + 8*S.card/((N : ℝ)*primeReciprocalMass S) := by
  classical
  let A := primeReciprocalMass S
  have hpoint (n : ℕ) : (if (primeDivisorCountIn S (n+1) : ℝ) ≤ A/2 then (1 : ℝ) else 0)*(A/2)^2 ≤
      ((primeDivisorCountIn S (n+1) : ℝ)-A)^2 := by
    split_ifs with h
    · simp only [one_mul]
      have hh := mul_nonneg (sub_nonneg.mpr h)
        (show 0 ≤ 2*A-A/2-(primeDivisorCountIn S (n+1) : ℝ) by dsimp [A] at *; linarith)
      nlinarith
    · simp only [zero_mul]
      positivity
  have hs := sum_le_sum (s := range N) fun n _ => hpoint n
  rw [← sum_mul] at hs
  simp only [sum_boole] at hs
  have hv := primeDivisorCountIn_variance_bound S hS N
  have htot : (((range N).filter fun n => (primeDivisorCountIn S (n+1) : ℝ) ≤ A/2).card : ℝ)*(A/2)^2 ≤
      N*A+2*A*S.card := hs.trans hv
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  change _ ≤ 4/A+8*S.card/((N : ℝ)*A)
  apply (div_le_iff₀ hNr).mpr
  have hA0 : A ≠ 0 := hA.ne'
  have he : (4/A+8*S.card/((N : ℝ)*A))*(N : ℝ)*(A/2)^2 = N*A+2*A*S.card := by
    field_simp
    ring
  have hpos : 0 < (A/2)^2 := by dsimp [A]; positivity
  nlinarith

/-- A finite bound for exponential suppression by the prime divisor count.
It will control the probability that a randomly chosen box receives none of
these primes. This is still a one-integer estimate, not a signed correlation. -/
theorem primeDivisorCountIn_power_mean_bound (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    (N : ℕ) (hN : 0 < N) (hA : 0 < primeReciprocalMass S)
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1) (L : ℕ) (hL : (L : ℝ) ≤ primeReciprocalMass S/2) :
    (∑ n ∈ range N, r^primeDivisorCountIn S (n+1))/N ≤
      4/primeReciprocalMass S+8*S.card/((N : ℝ)*primeReciprocalMass S)+r^L := by
  classical
  have hpoint (n : ℕ) : r^primeDivisorCountIn S (n+1) ≤
      (if (primeDivisorCountIn S (n+1) : ℝ) ≤ primeReciprocalMass S/2 then (1 : ℝ) else 0)+r^L := by
    split_ifs with h
    · have hb : r^primeDivisorCountIn S (n+1) ≤ 1 := pow_le_one₀ hr hr1
      have hnonneg : 0 ≤ r^L := pow_nonneg hr L
      linarith
    · have hcount : L ≤ primeDivisorCountIn S (n+1) := by
        exact_mod_cast hL.trans (le_of_not_ge h)
      simpa only [zero_add] using pow_le_pow_of_le_one hr hr1 hcount
  have hs := sum_le_sum (s := range N) fun n _ => hpoint n
  simp only [sum_add_distrib,sum_const,card_range,nsmul_eq_mul,sum_boole] at hs
  have hd := div_le_div_of_nonneg_right hs (Nat.cast_nonneg (α := ℝ) N)
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [add_div,mul_div_cancel_left₀ _ hN0] at hd
  exact hd.trans (add_le_add (primeDivisorCountIn_low_count_bound S hS N hN hA) le_rfl)

#print axioms primeDivisorCountIn_variance_bound
#print axioms primeDivisorCountIn_power_mean_bound
end Erdos371.FiniteSieve
