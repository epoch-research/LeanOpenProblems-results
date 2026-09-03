import Submission.FilteredPredecessorUnits
import Submission.FilteredGcdPolynomialBound

/-!
A uniform bound for the gcd of factorial-scaled filtered coefficients.
The constants here depend on the maximal filter degree, not on the endpoint.
This is auxiliary arithmetic, not a proof of Erdős Problem 68.
-/

namespace FilteredGcdUniformBound

open Finset BinomialFilteredLambert FilteredWindowGcd
  FilteredPredecessorUnits FilteredGcdPolynomialBound

lemma exists_small_power (p K : ℕ) (hp : p.Prime) (hK : 2 ≤ K) :
    ∃ r, K < p^(r+1) ∧ p^(r+1) ≤ p*(K+1) ∧
      (p^(r+1)-1)/(p-1) ≤ 2*(K+1) := by
  have hc : 0 < Nat.clog p (K+1) := Nat.clog_pos hp.one_lt (by omega)
  let r := Nat.clog p (K+1)-1
  have he : r+1=Nat.clog p (K+1) := by dsimp [r]; omega
  have hlow : K < p^(r+1) := by
    rw [he]
    exact (Nat.lt_succ_self K).trans_le (Nat.le_pow_clog hp.one_lt (K+1))
  have hhigh : p^(r+1) ≤ p*(K+1) := by
    rw [he]
    exact pow_clog_le_mul p (K+1) hp (by omega)
  refine ⟨r, hlow, hhigh, ?_⟩
  apply Nat.div_le_of_le_mul
  have hp2 := hp.two_le
  calc
    p^(r+1)-1 ≤ p*(K+1) := (Nat.sub_le _ _).trans hhigh
    _ ≤ (2*(p-1))*(K+1) :=
      Nat.mul_le_mul_right (K+1) (by omega : p ≤ 2*(p-1))
    _ = (p-1)*(2*(K+1)) := by ring

lemma prime_dvd_primorial (K p : ℕ) (hp : p.Prime) (hpK : p ≤ K) :
    p ∣ primorial K := by
  exact Finset.dvd_prod_of_mem (fun p : ℕ => p)
    ((mem_smallPrimes K p).mpr ⟨hp, hpK⟩)

/-- The whole gcd divides the endpoint times a fixed primorial power.
Only a quadratic additional window width is needed. -/
theorem filtered_window_gcd_dvd_primorial (ks : List ℕ) (K H N : ℕ)
    (hH : 2 ≤ H) (hHN : 2*H ≤ N) (hwide : H+K*(K+1) ≤ N)
    (hks : ∀ k ∈ ks, 2 ≤ k ∧ k ≤ K) :
    windowGcd (filtered ks) H N ∣ N*(primorial K)^(2*(K+1)) := by
  have hN : 0 < N := by omega
  have hM : 0 < (primorial K)^(2*(K+1)) := Nat.pow_pos (primorial_pos K)
  apply (Nat.factorization_prime_le_iff_dvd
    (windowGcd_pos (filtered ks) H N).ne' (Nat.mul_pos hN hM).ne').mp
  intro p hp
  rw [Nat.factorization_mul hN.ne' hM.ne', Finsupp.add_apply]
  by_cases hpK : p ≤ K
  · obtain ⟨r, hlow, hhigh, hr⟩ := exists_small_power p K hp (hp.two_le.trans hpK)
    have hwidthp : H+p^(r+1) ≤ N := by
      exact (Nat.add_le_add_left
        (hhigh.trans (Nat.mul_le_mul_right (K+1) hpK)) H).trans hwide
    have hv := filtered_window_valuation_bound_div ks p r H N hp hH hwidthp
      (fun k hk => ⟨(hks k hk).1, (hks k hk).2.trans_lt hlow⟩)
    have hdiv := pow_dvd_pow_of_dvd (prime_dvd_primorial K p hp hpK) (2*(K+1))
    have he : 2*(K+1) ≤ ((primorial K)^(2*(K+1))).factorization p := by
      have hf := (Nat.factorization_le_iff_dvd
        (pow_ne_zero _ hp.ne_zero) hM.ne').mpr hdiv
      simpa only [Nat.factorization_pow_self hp] using hf p
    exact hv.trans (Nat.add_le_add_left (hr.trans he) _)
  · have hv := filtered_window_prime_valuation_bound ks p H N hp hH hHN
      (fun k hk => ⟨(hks k hk).1, by have := (hks k hk).2; omega⟩)
    exact hv.trans (Nat.le_add_right _ _)

/-- An elementary exponential version of the bound, uniform in K. -/
theorem filtered_window_gcd_le (ks : List ℕ) (K H N : ℕ)
    (hH : 2 ≤ H) (hHN : 2*H ≤ N) (hwide : H+K*(K+1) ≤ N)
    (hks : ∀ k ∈ ks, 2 ≤ k ∧ k ≤ K) :
    windowGcd (filtered ks) H N ≤ N*16^(K*(K+1)) := by
  have hN : 0 < N := by omega
  calc
    windowGcd (filtered ks) H N ≤ N*(primorial K)^(2*(K+1)) :=
      Nat.le_of_dvd (Nat.mul_pos hN (Nat.pow_pos (primorial_pos K)))
        (filtered_window_gcd_dvd_primorial ks K H N hH hHN hwide hks)
    _ ≤ N*(4^K)^(2*(K+1)) := Nat.mul_le_mul_left N
      (Nat.pow_le_pow_left (primorial_le_4_pow K) _)
    _ = N*16^(K*(K+1)) := by
      congr 1
      calc
        (4^K)^(2*(K+1)) = (4^2)^(K*(K+1)) := by
          simp only [← pow_mul]
          congr 1
          ring
        _ = _ := by norm_num

/-- A factorial remains in every simultaneous clearing multiplier for the
individual coefficients, up to the fixed primorial factor. -/
theorem factorial_pred_dvd_commonDenominator (ks : List ℕ) (K H N : ℕ)
    (hH : 2 ≤ H) (hHN : 2*H ≤ N) (hwide : H+K*(K+1) ≤ N)
    (hks : ∀ k ∈ ks, 2 ≤ k ∧ k ≤ K) :
    (N-1).factorial ∣ (primorial K)^(2*(K+1))*
      commonDenominator (filtered ks) H N := by
  have hN : 0 < N := by omega
  have hd := Nat.mul_dvd_mul_left (commonDenominator (filtered ks) H N)
    (filtered_window_gcd_dvd_primorial ks K H N hH hHN hwide hks)
  rw [commonDenominator_mul_gcd] at hd
  have he : commonDenominator (filtered ks) H N*(N*(primorial K)^(2*(K+1))) =
      N*((primorial K)^(2*(K+1))*commonDenominator (filtered ks) H N) := by ring
  rw [he] at hd
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN.ne'
  simpa only [Nat.add_sub_cancel, Nat.factorial_succ,
    Nat.mul_dvd_mul_iff_left (Nat.succ_pos n)] using hd

end FilteredGcdUniformBound

#print axioms FilteredGcdUniformBound.filtered_window_gcd_dvd_primorial
#print axioms FilteredGcdUniformBound.filtered_window_gcd_le
#print axioms FilteredGcdUniformBound.factorial_pred_dvd_commonDenominator
