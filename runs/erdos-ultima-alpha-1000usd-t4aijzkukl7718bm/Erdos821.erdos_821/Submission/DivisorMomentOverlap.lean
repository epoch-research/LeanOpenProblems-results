import Submission.WeightedRoughPrimes

/-!
# Overlap in squaring a divisor count

This records an obstruction to a pointwise Cauchy--Schwarz shortcut, not
an obstruction to Erdős 821 itself. On actual shifted primes, the square
of the two-fold divisor count is not uniformly bounded by the three-fold
count. Common prime factors of the two divisors cannot be ignored.
-/

open Nat Filter ArithmeticFunction
open scoped Classical BigOperators ArithmeticFunction.zeta ArithmeticFunction.sigma Topology

namespace Erdos821.HigherDivisors

lemma tau_factorization (k n : ℕ) (hn : n ≠ 0) :
    tau k n = ∏ p ∈ n.primeFactors, tau k (p^(n.factorization p)) := by
  exact (tau_multiplicative k).multiplicative_factorization _ hn

lemma tau_succ_pos (k n : ℕ) (hn : n ≠ 0) : 0 < tau (k+1) n := by
  rw [tau_succ]
  have hmem : 1 ∈ n.divisors := Nat.one_mem_divisors.mpr hn
  have hle := Finset.single_le_sum (fun d (_ : d ∈ n.divisors) => Nat.zero_le (tau k d)) hmem
  have h1 : tau k 1 = 1 := (tau_multiplicative k).map_one
  omega

lemma tau_two_sq_prime_power (p e : ℕ) (hp : p.Prime) (he : 1 ≤ e) :
    (4/3 : ℝ)*(tau 3 (p^e) : ℝ) ≤ (tau 2 (p^e) : ℝ)^2 := by
  rw [tau_prime_pow 2 e p hp, tau_prime_pow 1 e p hp, Nat.choose_one_right]
  have hc : (e+2)*(e+1) = (e+2).choose 2 * 2 := by
    simpa only [Nat.choose_one_right, Nat.add_assoc] using Nat.add_one_mul_choose_eq (e+1) 1
  have hcR : ((e : ℝ)+2)*((e : ℝ)+1) = ((e+2).choose 2 : ℝ)*2 := by
    exact_mod_cast hc
  have heR : (1 : ℝ) ≤ e := by exact_mod_cast he
  push_cast
  nlinarith [sq_nonneg ((e : ℝ)-1)]

/-- Every distinct prime factor contributes a factor at least 4/3 to
this overlap ratio, independently of its positive exponent. -/
theorem tau_two_sq_ge_primeFactors (n : ℕ) (hn : n ≠ 0) :
    (4/3 : ℝ)^n.primeFactors.card * (tau 3 n : ℝ) ≤ (tau 2 n : ℝ)^2 := by
  rw [tau_factorization 3 n hn, tau_factorization 2 n hn]
  push_cast
  rw [← Finset.prod_pow, ← Finset.prod_const, ← Finset.prod_mul_distrib]
  apply Finset.prod_le_prod
  · intro p hp
    positivity
  · intro p hp
    have hp' := Nat.prime_of_mem_primeFactors hp
    exact tau_two_sq_prime_power p (n.factorization p) hp'
      (hp'.factorization_pos_of_dvd hn (Nat.dvd_of_mem_primeFactors hp))

/-- Dirichlet's theorem gives arbitrarily large shifted primes with
arbitrarily many specified distinct prime factors in their predecessor. -/
lemma exists_prime_with_many_predecessor_factors (r B : ℕ) :
    ∃ p : ℕ, B < p ∧ p.Prime ∧ r ≤ (p-1).primeFactors.card := by
  obtain ⟨S, hS, hcard⟩ := Nat.infinite_setOf_prime.exists_subset_card_eq r
  have hSp (q : ℕ) (hq : q ∈ S) : q.Prime := hS hq
  let M : ℕ := ∏ q ∈ S, q
  have hM : M ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun q hq => (hSp q hq).ne_zero)
  obtain ⟨p, hpB, hp, hmod⟩ := Nat.forall_exists_prime_gt_and_modEq (B+1) hM (Nat.coprime_one_left M)
  have hn : p-1 ≠ 0 := by have := hp.one_lt; omega
  have hdiv : M ∣ p-1 := (Nat.modEq_iff_dvd' hp.one_lt.le).mp hmod.symm
  have hmono := Nat.primeFactors_mono hdiv hn
  have heq : M.primeFactors = S := Nat.primeFactors_prod hSp
  rw [heq] at hmono
  refine ⟨p, by omega, hp, ?_⟩
  rw [← hcard]
  exact Finset.card_le_card hmono

/-- No constant can absorb divisor-pair overlaps, even after restricting
to arbitrarily large shifted primes. -/
theorem exists_shifted_prime_divisor_overlap_gt (C : ℝ) (B : ℕ) :
    ∃ p : ℕ, B < p ∧ p.Prime ∧ C*(tau 3 (p-1) : ℝ) < (tau 2 (p-1) : ℝ)^2 := by
  obtain ⟨r, hr⟩ := pow_unbounded_of_one_lt C (by norm_num : (1 : ℝ) < 4/3)
  obtain ⟨p, hpB, hp, hpr⟩ := exists_prime_with_many_predecessor_factors r B
  have hn : p-1 ≠ 0 := by have := hp.one_lt; omega
  have ht : (0 : ℝ) < tau 3 (p-1) := by exact_mod_cast tau_succ_pos 2 (p-1) hn
  refine ⟨p,hpB,hp,?_⟩
  calc
    _ < (4/3 : ℝ)^r * (tau 3 (p-1) : ℝ) := mul_lt_mul_of_pos_right hr ht
    _ ≤ (4/3 : ℝ)^(p-1).primeFactors.card * (tau 3 (p-1) : ℝ) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hpr) ht.le
    _ ≤ _ := tau_two_sq_ge_primeFactors (p-1) hn

theorem not_eventually_uniform_shifted_prime_overlap (C : ℝ) :
    ¬∀ᶠ p : ℕ in atTop, p.Prime → (tau 2 (p-1) : ℝ)^2 ≤ C*(tau 3 (p-1) : ℝ) := by
  intro h
  obtain ⟨B,hB⟩ := eventually_atTop.mp h
  obtain ⟨p,hpB,hp,hh⟩ := exists_shifted_prime_divisor_overlap_gt C B
  exact (hB p hpB.le hp).not_gt hh


lemma tau_two_eq_divisors_card (n : ℕ) : tau 2 n = n.divisors.card := by
  have h : (ζ : ArithmeticFunction ℕ)*ζ = σ 0 := by
    simpa only [pow_zero_eq_zeta] using (zeta_mul_pow_eq_sigma (k := 0))
  simp only [tau, pow_two, h, sigma_zero_apply]

lemma tau_two_sq_le_tau_four (n : ℕ) : (tau 2 n : ℝ)^2 ≤ (tau 4 n : ℝ) := by
  rw [tau_two_eq_divisors_card, tau_cast]
  exact AnalyticSieve.divisor_card_sq_le_zeta_four n

noncomputable def shiftedPrimeMoment (k X : ℕ) : ℝ :=
  ∑ p ∈ (X+1).primesBelow, (tau k (p-1) : ℝ)

/-- The direct Cauchy--Schwarz implication lands at divisor order four,
not order three. -/
theorem shiftedPrimeMoment_two_sq_le_four (X : ℕ) :
    (shiftedPrimeMoment 2 X)^2 ≤ ((X+1).primesBelow.card : ℝ)*shiftedPrimeMoment 4 X := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (X+1).primesBelow
    (fun _ => (1 : ℝ)) (fun p => (tau 2 (p-1) : ℝ))
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at h
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  exact Finset.sum_le_sum (fun p _ => tau_two_sq_le_tau_four (p-1))

end Erdos821.HigherDivisors
