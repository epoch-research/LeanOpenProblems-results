import Submission.PrimeCountExponentialMoment

/-! Uniform integrability of exponential pattern weights for arbitrary prime
sets of bounded reciprocal mass. This is an absolute upper estimate, not a
signed correlation or independence theorem. -/
namespace Erdos371.FiniteSieve
open Finset Filter
open scoped Topology

lemma activeBlockPrimes_exp_moment_mean (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (z M : ℝ) (hz : 1 ≤ z) (hM : primeReciprocalMass P ≤ M) (N : ℕ) (hN : 0 < N) :
    (∑ n ∈ range N, z^(activeBlockPrimes P (activePrimeAtoms P (n+1))).card)/(N : ℝ) ≤
      2*Real.exp ((z^2-1)*M) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hcoef : 0 ≤ z^2-1 := sub_nonneg.mpr (one_le_pow₀ hz)
  have hexp : Real.exp ((z^2-1)*primeReciprocalMass P) ≤ Real.exp ((z^2-1)*M) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hM hcoef)
  apply (div_le_iff₀ hNr).mpr
  calc
    _ ≤ (N+1 : ℝ)*Real.exp ((z^2-1)*primeReciprocalMass P) :=
      activeBlockPrimes_exp_moment_sum P hP z hz N
    _ ≤ (2*N)*Real.exp ((z^2-1)*M) := mul_le_mul (by linarith) hexp (by positivity) (by positivity)
    _ = _ := by ring

lemma two_power_high_count_bound (L m : ℕ) :
    (if L ≤ m then (2 : ℝ)^m else 0) ≤ (4 : ℝ)^m/(2 : ℝ)^L := by
  split_ifs with hm
  · apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2^L)).mpr
    calc
      _ ≤ (2 : ℝ)^m*2^m := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) hm) (by positivity)
      _ = _ := by rw [← pow_two,← pow_mul,mul_comm m 2,pow_mul]; norm_num
  · positivity

/-- Exponential active-count tails have a uniform geometric bound. There is
NO small-power restriction on the primes in P. -/
theorem prime_pattern_exponential_tail_bound (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (M : ℝ) (hM : primeReciprocalMass P ≤ M) (N L : ℕ) (hN : 0 < N) :
    (∑ n ∈ range N, if L ≤ (activeBlockPrimes P (activePrimeAtoms P (n+1))).card then
      (2 : ℝ)^(activeBlockPrimes P (activePrimeAtoms P (n+1))).card else 0)/(N : ℝ) ≤
      2*Real.exp (15*M)/(2 : ℝ)^L := by
  have h := activeBlockPrimes_exp_moment_mean P hP 4 M (by norm_num) hM N hN
  norm_num only [show (4 : ℝ)^2-1=15 by norm_num] at h
  calc
    _ ≤ (∑ n ∈ range N, (4 : ℝ)^(activeBlockPrimes P (activePrimeAtoms P (n+1))).card/2^L)/(N : ℝ) :=
      div_le_div_of_nonneg_right (sum_le_sum fun n _ => two_power_high_count_bound L _) (Nat.cast_nonneg N)
    _ = ((∑ n ∈ range N, (4 : ℝ)^(activeBlockPrimes P (activePrimeAtoms P (n+1))).card)/(N : ℝ))/2^L := by
      rw [← sum_div]
      ring
    _ ≤ _ := div_le_div_of_nonneg_right h (by positivity)

/-- An upper-tail threshold works for ALL positive N and ALL prime sets of
the given mass, not just eventually for primes below a chosen power of N. -/
theorem prime_pattern_exponential_tail_uniform (M ε : ℝ) (hε : 0 < ε) :
    ∃ L : ℕ, ∀ N : ℕ, 0 < N → ∀ P : Finset ℕ,
      (∀ p ∈ P, p.Prime) → primeReciprocalMass P ≤ M →
      (∑ n ∈ range N, if L ≤ (activeBlockPrimes P (activePrimeAtoms P (n+1))).card then
        (2 : ℝ)^(activeBlockPrimes P (activePrimeAtoms P (n+1))).card else 0)/(N : ℝ) < ε := by
  obtain ⟨L,hL⟩ := exists_nat_gt (2*Real.exp (15*M)/ε)
  have hpow : (L : ℝ) < (2 : ℝ)^L := by exact_mod_cast (Nat.lt_two_pow_self (n := L))
  have hs : 2*Real.exp (15*M)/(2 : ℝ)^L < ε := by
    apply (div_lt_iff₀ (by positivity : (0 : ℝ) < 2^L)).mpr
    have h := (div_lt_iff₀ hε).mp (hL.trans hpow)
    nlinarith
  exact ⟨L,fun N hN P hP hM => (prime_pattern_exponential_tail_bound P hP M hM N L hN).trans_lt hs⟩

lemma weighted_subset_sum_sq_le {ι : Type*} (E X : Finset ι) (hE : E ⊆ X) (w : ι → ℝ) :
    (∑ n ∈ E, w n)^2 ≤ (E.card : ℝ)*(∑ n ∈ X, (w n)^2) := by
  have h := sum_mul_sq_le_sq_mul_sq E (fun _ => (1 : ℝ)) w
  simp only [one_mul,one_pow,sum_const,nsmul_eq_mul,mul_one] at h
  exact h.trans (mul_le_mul_of_nonneg_left
    (sum_le_sum_of_subset_of_nonneg hE (fun n _ _ => sq_nonneg _)) (Nat.cast_nonneg _))

/-- Exponential weights on an arbitrary exceptional set are controlled by
its density. This does not assume independence of the exceptional set. -/
theorem prime_pattern_exponential_exception_sq (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (M : ℝ) (hM : primeReciprocalMass P ≤ M) (N : ℕ) (hN : 0 < N)
    (E : Finset ℕ) (hE : E ⊆ range N) :
    ((∑ n ∈ E, (2 : ℝ)^(activeBlockPrimes P (activePrimeAtoms P (n+1))).card)/(N : ℝ))^2 ≤
      (E.card : ℝ)/N*(2*Real.exp (15*M)) := by
  have h := weighted_subset_sum_sq_le E (range N) hE
    (fun n => (2 : ℝ)^(activeBlockPrimes P (activePrimeAtoms P (n+1))).card)
  have he (m : ℕ) : ((2 : ℝ)^m)^2=(4 : ℝ)^m := by
    rw [← pow_mul,mul_comm m 2,pow_mul]
    norm_num
  simp_rw [he] at h
  have hm := activeBlockPrimes_exp_moment_mean P hP 4 M (by norm_num) hM N hN
  norm_num only [show (4 : ℝ)^2-1=15 by norm_num] at hm
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hsum := (div_le_iff₀ hNr).mp hm
  have hh := h.trans (mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg E.card))
  rw [div_pow]
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < (N : ℝ)^2)).mpr
  convert hh using 1
  field_simp

/-- Uniform bounded mass and a density-zero exceptional set give vanishing
mean of the full exponential weight on that set. -/
theorem prime_pattern_exponential_exception_zero (P : ℕ → Finset ℕ) (E : ℕ → Finset ℕ) (M : ℝ)
    (hdata : ∀ᶠ N : ℕ in atTop,
      (∀ p ∈ P N, p.Prime) ∧ primeReciprocalMass (P N) ≤ M ∧ E N ⊆ range N)
    (hE : Tendsto (fun N : ℕ => ((E N).card : ℝ)/N) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ =>
      (∑ n ∈ E N, (2 : ℝ)^(activeBlockPrimes (P N) (activePrimeAtoms (P N) (n+1))).card)/N)
      atTop (𝓝 0) := by
  have ht := hE.mul_const (2*Real.exp (15*M))
  simp only [zero_mul] at ht
  have hs : Tendsto (fun N : ℕ =>
      ((∑ n ∈ E N, (2 : ℝ)^(activeBlockPrimes (P N) (activePrimeAtoms (P N) (n+1))).card)/N)^2)
      atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall fun N => sq_nonneg _) _ ht
    filter_upwards [hdata,eventually_gt_atTop (0 : ℕ)] with N hd hN
    exact prime_pattern_exponential_exception_sq (P N) hd.1 M hd.2.1 N hN (E N) hd.2.2
  have h := hs.sqrt
  simpa only [Real.sqrt_zero,Real.sqrt_sq_eq_abs,
    abs_of_nonneg (div_nonneg (sum_nonneg fun n _ => pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _) (Nat.cast_nonneg _))] using h

#print axioms prime_pattern_exponential_tail_uniform
#print axioms prime_pattern_exponential_exception_zero
end Erdos371.FiniteSieve
