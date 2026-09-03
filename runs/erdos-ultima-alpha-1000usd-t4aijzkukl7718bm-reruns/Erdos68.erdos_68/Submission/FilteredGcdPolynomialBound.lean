import Submission.FilteredPeriodicUnits

/-!
A polynomial upper bound, for fixed filters, on the common gcd of
factorial-scaled individual coefficients in sufficiently long windows.
This does not bound a Bézout lift or settle Erdős Problem 68.
-/

namespace FilteredGcdPolynomialBound

open Finset FilteredCoefficientGcd FilteredWindowGcd
  BinomialFilteredLambert FilteredPeriodicUnits

def smallPrimes (K : ℕ) : Finset ℕ :=
  (Finset.range (K+1)).filter Nat.Prime

lemma mem_smallPrimes (K p : ℕ) : p ∈ smallPrimes K ↔ p.Prime ∧ p ≤ K := by
  simp only [smallPrimes, Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff]
  tauto

def smallModulus (K N : ℕ) : ℕ :=
  ∏ p ∈ smallPrimes K, p^(p^(K+2)*Nat.clog p N)

def primeConstant (K : ℕ) : ℕ :=
  ∏ p ∈ smallPrimes K, p^(p^(K+2))

def primeExponent (K : ℕ) : ℕ :=
  ∑ p ∈ smallPrimes K, p^(K+2)

lemma smallModulus_pos (K N : ℕ) : 0 < smallModulus K N := by
  apply Finset.prod_pos
  intro p hp
  exact Nat.pow_pos ((mem_smallPrimes K p).mp hp).1.pos

lemma primeConstant_pos (K : ℕ) : 0 < primeConstant K := by
  apply Finset.prod_pos
  intro p hp
  exact Nat.pow_pos ((mem_smallPrimes K p).mp hp).1.pos

/-- Large primes contribute only the current index; small primes contribute
an explicitly bounded power. This is an assertion about the whole gcd. -/
theorem filtered_window_gcd_dvd (ks : List ℕ) (K H N : ℕ)
    (hH : 2 ≤ H) (hHN : 2*H ≤ N)
    (hwide : H+K^(K+2) ≤ N)
    (hks : ∀ k ∈ ks, 2 ≤ k ∧ k ≤ K) :
    windowGcd (filtered ks) H N ∣ N*smallModulus K N := by
  have hN : 0 < N := by omega
  have hM := smallModulus_pos K N
  apply (Nat.factorization_prime_le_iff_dvd
    (windowGcd_pos (filtered ks) H N).ne' (Nat.mul_pos hN hM).ne').mp
  intro p hp
  by_cases hpK : p ≤ K
  · have hwidep : H+p^(K+2) ≤ N :=
      (Nat.add_le_add_left (Nat.pow_le_pow_left hpK _) H).trans hwide
    have hbound := filtered_window_small_prime_bound ks p K H N hp hwidep
      (fun k hk => ⟨by have := hks k hk; omega,
        lt_of_le_of_lt (hks k hk).2
          (lt_trans (Nat.lt_succ_self K) (Nat.lt_pow_self hp.one_lt))⟩)
    have hmem : p ∈ smallPrimes K := (mem_smallPrimes K p).mpr ⟨hp, hpK⟩
    have hdiv : p^(p^(K+2)*Nat.clog p N) ∣ smallModulus K N :=
      Finset.dvd_prod_of_mem _ hmem
    have hv := (Nat.factorization_le_iff_dvd
      (pow_ne_zero _ hp.ne_zero) hM.ne').mpr hdiv
    have hleft : p^(K+2)*Nat.clog p N ≤ (smallModulus K N).factorization p := by
      simpa only [Nat.factorization_pow_self hp] using hv p
    exact (hbound.trans hleft).trans
      (Nat.factorization_le_factorization_mul_right hN.ne' p)
  · have hbound := filtered_window_prime_valuation_bound ks p H N hp hH hHN
      (fun k hk => ⟨(hks k hk).1, by have := (hks k hk).2; omega⟩)
    exact hbound.trans (Nat.factorization_le_factorization_mul_left hM.ne' p)

lemma pow_clog_le_mul (p N : ℕ) (hp : p.Prime) (hN : 0 < N) :
    p^Nat.clog p N ≤ p*N := by
  by_cases hN1 : N=1
  · subst N
    simpa using hp.one_lt.le
  · have hN2 : 1 < N := by omega
    have hc := Nat.clog_pos hp.one_lt hN2
    have hl := Nat.pow_pred_clog_lt_self hp.one_lt hN2
    have he : Nat.clog p N = (Nat.clog p N).pred+1 :=
      (Nat.succ_pred_eq_of_pos hc).symm
    rw [he, pow_succ]
    simpa only [Nat.mul_comm] using Nat.mul_le_mul_right p hl.le

lemma smallModulus_le_polynomial (K N : ℕ) (hN : 0 < N) :
    smallModulus K N ≤ primeConstant K * N^primeExponent K := by
  calc
    smallModulus K N ≤ ∏ p ∈ smallPrimes K, (p*N)^(p^(K+2)) := by
      apply Finset.prod_le_prod'
      intro p hp
      have hprime := ((mem_smallPrimes K p).mp hp).1
      rw [Nat.mul_comm (p^(K+2)), pow_mul]
      exact Nat.pow_le_pow_left (pow_clog_le_mul p N hprime hN) _
    _ = primeConstant K * N^primeExponent K := by
      simp_rw [mul_pow]
      rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
      rfl

/-- With K fixed, both the exponent and constant are independent of H,N.
The lower bound on the window width also depends on K. -/
theorem filtered_window_gcd_le_polynomial (ks : List ℕ) (K H N : ℕ)
    (hH : 2 ≤ H) (hHN : 2*H ≤ N)
    (hwide : H+K^(K+2) ≤ N)
    (hks : ∀ k ∈ ks, 2 ≤ k ∧ k ≤ K) :
    windowGcd (filtered ks) H N ≤ primeConstant K * N^(primeExponent K+1) := by
  have hN : 0 < N := by omega
  calc
    windowGcd (filtered ks) H N ≤ N*smallModulus K N :=
      Nat.le_of_dvd (Nat.mul_pos hN (smallModulus_pos K N))
        (filtered_window_gcd_dvd ks K H N hH hHN hwide hks)
    _ ≤ N*(primeConstant K*N^primeExponent K) :=
      Nat.mul_le_mul_left _ (smallModulus_le_polynomial K N hN)
    _ = primeConstant K*N^(primeExponent K+1) := by rw [pow_succ]; ring


/-- The quotient that clears all individual coefficients in the window.
It is not the reduced denominator of their sum. -/
def commonDenominator (a : ℕ → ℤ) (H N : ℕ) : ℕ :=
  N.factorial / windowGcd a H N

lemma commonDenominator_pos (a : ℕ → ℤ) (H N : ℕ) :
    0 < commonDenominator a H N := by
  exact Nat.div_pos (Nat.le_of_dvd (Nat.factorial_pos N)
    (windowGcd_dvd_factorial a H N)) (windowGcd_pos a H N)

lemma commonDenominator_mul_gcd (a : ℕ → ℤ) (H N : ℕ) :
    commonDenominator a H N * windowGcd a H N = N.factorial :=
  Nat.div_mul_cancel (windowGcd_dvd_factorial a H N)

lemma commonDenominator_dvd_iff (a : ℕ → ℤ) (H N d : ℕ) :
    commonDenominator a H N ∣ d ↔
      ∀ k ∈ Finset.Icc H N, N.factorial ∣ d*scaledCoeff a N k := by
  rw [commonDenominator, Nat.div_dvd_iff_dvd_mul
    (windowGcd_dvd_factorial a H N) (windowGcd_pos a H N)]
  constructor
  · intro h k hk
    rw [Nat.mul_comm (windowGcd a H N) d] at h
    exact h.trans (Nat.mul_dvd_mul_left d (windowGcd_dvd_scaled a H N k hk))
  · intro h
    have hd : N.factorial ∣ Nat.gcd (d*N.factorial)
        ((Finset.Icc H N).gcd (fun k => d*scaledCoeff a N k)) :=
      Nat.dvd_gcd (Nat.dvd_mul_left _ _) (Finset.dvd_gcd_iff.mpr h)
    rw [Finset.gcd_mul_left] at hd
    simpa [gcd_eq_nat_gcd, Nat.gcd_mul_left, Nat.gcd_mul_right, windowGcd, Nat.mul_comm d] using hd

lemma int_fraction_integral_iff (z : ℤ) (n : ℕ) (hn : 0 < n) :
    (∃ m : ℤ, (z : ℚ)/n=m) ↔ (n : ℤ) ∣ z := by
  have hnq : (n : ℚ) ≠ 0 := by positivity
  constructor
  · rintro ⟨m, hm⟩
    refine ⟨m, ?_⟩
    have he := (div_eq_iff hnq).mp hm
    exact_mod_cast (he.trans (mul_comm (m : ℚ) n))
  · rintro ⟨m, hm⟩
    refine ⟨m, ?_⟩
    rw [hm]
    push_cast
    field_simp

lemma individual_clearing_iff (a : ℕ → ℤ) (N k d : ℕ) (hk : k ≤ N) :
    (∃ z : ℤ, (d : ℚ)*(a k : ℚ)/k.factorial=z) ↔
      N.factorial ∣ d*scaledCoeff a N k := by
  have hcast : (d : ℚ)*(a k : ℚ) = ((d : ℤ)*a k : ℤ) := by push_cast; rfl
  rw [hcast, int_fraction_integral_iff _ _ (Nat.factorial_pos k), Int.natCast_dvd]
  simp only [Int.natAbs_mul, Int.natAbs_natCast]
  have hf := Nat.div_mul_cancel (Nat.factorial_dvd_factorial hk)
  have hq := factorial_quotient_pos k N hk
  conv_rhs => rw [← hf]
  rw [scaledCoeff]
  have he : d*((a k).natAbs*(N.factorial/k.factorial)) =
      (N.factorial/k.factorial)*(d*(a k).natAbs) := by ring
  rw [he, Nat.mul_dvd_mul_iff_left hq]

/-- This proves the exact common-denominator interpretation of the gcd
quotient, including minimality among natural clearing multipliers. -/
theorem commonDenominator_dvd_iff_integral (a : ℕ → ℤ) (H N d : ℕ) :
    commonDenominator a H N ∣ d ↔
      ∀ k ∈ Finset.Icc H N, ∃ z : ℤ, (d : ℚ)*(a k : ℚ)/k.factorial=z := by
  rw [commonDenominator_dvd_iff]
  constructor
  · intro h k hk
    exact (individual_clearing_iff a N k d (Finset.mem_Icc.mp hk).2).mpr (h k hk)
  · intro h k hk
    exact (individual_clearing_iff a N k d (Finset.mem_Icc.mp hk).2).mp (h k hk)

/-- A fixed filter can remove at most a polynomial factor from this common
factorial denominator. This says nothing about an aggregate weighted sum. -/
theorem factorial_le_polynomial_mul_commonDenominator
    (ks : List ℕ) (K H N : ℕ)
    (hH : 2 ≤ H) (hHN : 2*H ≤ N) (hwide : H+K^(K+2) ≤ N)
    (hks : ∀ k ∈ ks, 2 ≤ k ∧ k ≤ K) :
    N.factorial ≤ (primeConstant K*N^(primeExponent K+1))*
      commonDenominator (filtered ks) H N := by
  have hb := filtered_window_gcd_le_polynomial ks K H N hH hHN hwide hks
  calc
    N.factorial = windowGcd (filtered ks) H N *
        commonDenominator (filtered ks) H N := by
      rw [Nat.mul_comm, commonDenominator_mul_gcd]
    _ ≤ _ := Nat.mul_le_mul_right _ hb

end FilteredGcdPolynomialBound

#print axioms FilteredGcdPolynomialBound.filtered_window_gcd_dvd
#print axioms FilteredGcdPolynomialBound.filtered_window_gcd_le_polynomial
#print axioms FilteredGcdPolynomialBound.commonDenominator_dvd_iff_integral
#print axioms FilteredGcdPolynomialBound.factorial_le_polynomial_mul_commonDenominator
