import Submission.ExactColoringCost
import Submission.PrimeStripping

/-!
# Prime-exponent profiles in the coloring test

A large-factor occurrence can cover at most one rough input-prime occurrence.
The split higher-divisor bound makes this same loss explicit in the coloring
cost. No new lower estimate for smooth shifted primes is assumed or asserted.
-/

open Nat Filter ArithmeticFunction
open scoped Classical BigOperators ArithmeticFunction.zeta
namespace Erdos821
open HigherDivisors
set_option maxHeartbeats 3000000

/-- Prime factors at least y are counted with multiplicity. -/
noncomputable def upperFactorMass (n y : ℕ) : ℕ :=
  ∑ q ∈ n.primeFactors with y ≤ q, n.factorization q

/-- The divisor count of the part supported on primes strictly below y. -/
noncomputable def lowerDivisorCost (n y : ℕ) : ℕ :=
  ∏ q ∈ n.primeFactors with q < y, (n.factorization q+1)

lemma tau_prime_pow_le_colors (r e p : ℕ) (hr : 1 ≤ r) (hp : p.Prime) :
    tau r (p^e) ≤ r^e := by
  have hr' : r-1+1 = r := Nat.sub_add_cancel hr
  induction e with
  | zero =>
    simp only [pow_zero]
    exact (tau_multiplicative r).map_one.le
  | succ e ih =>
    have h := tau_prime_pow_succ_le (r-1) e p hp
    rw [hr'] at h
    simpa only [Nat.pow_succ'] using h.trans (Nat.mul_le_mul_left r ih)

lemma tau_prime_pow_le_small_cost (r e p : ℕ) (hr : 1 ≤ r) (hp : p.Prime) :
    tau r (p^e) ≤ (e+1)^(r-1) := by
  have h := tau_succ_le_divisors_pow (r-1) (p^e)
  rw [Nat.sub_add_cancel hr] at h
  have hc : (p^e).divisors.card = e+1 := by
    simpa using Nat.sum_divisors_prime_pow (k := e) (f := fun _ : ℕ => (1 : ℕ)) hp
  rwa [hc] at h

/-- Uniform in r: small primes cost divisor choices, large primes cost their
full exponent multiplicity. -/
theorem tau_le_split_prime_profile (r n y : ℕ) (hr : 1 ≤ r) (hn : 0 < n) :
    tau r n ≤ lowerDivisorCost n y^(r-1)*r^(upperFactorMass n y) := by
  have ht := (tau_multiplicative r).multiplicative_factorization
    ((ζ : ArithmeticFunction ℕ)^r) hn.ne'
  change tau r n = _ at ht
  rw [ht]
  simp only [Finsupp.prod,Nat.support_factorization]
  change (∏ p ∈ n.primeFactors, tau r (p^(n.factorization p))) ≤ _
  rw [← Finset.prod_filter_mul_prod_filter_not n.primeFactors (fun p => p < y)]
  simp only [not_lt]
  calc
    _ ≤ (∏ p ∈ n.primeFactors with p < y, (n.factorization p+1)^(r-1))*
        (∏ p ∈ n.primeFactors with y ≤ p, r^(n.factorization p)) := by
      apply Nat.mul_le_mul
      · exact Finset.prod_le_prod' (fun p hp => tau_prime_pow_le_small_cost r
          (n.factorization p) p hr (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1))
      · exact Finset.prod_le_prod' (fun p hp => tau_prime_pow_le_colors r
          (n.factorization p) p hr (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1))
    _ = _ := by rw [Finset.prod_pow,Finset.prod_pow_eq_pow_sum]; rfl

/-- Every rough member of an admissible support uses an occurrence among the
large prime factors of the output. This does not require squarefree inputs. -/
theorem admissibleSupport_rough_card_le_upperFactorMass
    (n y : ℕ) (hn : 0 < n) (S : Finset ℕ) (hS : S ∈ admissibleSupports n) :
    (S.filter (fun p => p-1 ∉ Nat.smoothNumbers y)).card ≤ upperFactorMass n y := by
  let Q := n.primeFactors.filter (fun q => y ≤ q)
  have hsub : S.filter (fun p => p-1 ∉ Nat.smoothNumbers y) ⊆
      Q.biUnion (fun q => S.filter (fun p => q ∣ p-1)) := by
    intro p hp
    obtain ⟨hpS,hprough⟩ := Finset.mem_filter.mp hp
    have hpd : p-1 ∣ n :=
      (Finset.mem_filter.mp (Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1 hpS)).2.2
    have hh : ¬∀ q, q.Prime → q ∣ p-1 → q < y :=
      fun h => hprough (Nat.mem_smoothNumbers'.mpr h)
    push_neg at hh
    obtain ⟨q,hqp,hqd,hqy⟩ := hh
    have hqQ : q ∈ Q := Finset.mem_filter.mpr
      ⟨Nat.mem_primeFactors.mpr ⟨hqp,hqd.trans hpd,hn.ne'⟩,hqy⟩
    exact Finset.mem_biUnion.mpr ⟨q,hqQ,Finset.mem_filter.mpr ⟨hpS,hqd⟩⟩
  calc
    _ ≤ (Q.biUnion (fun q => S.filter (fun p => q ∣ p-1))).card := Finset.card_le_card hsub
    _ ≤ ∑ q ∈ Q, (S.filter (fun p => q ∣ p-1)).card := Finset.card_biUnion_le
    _ ≤ upperFactorMass n y := Finset.sum_le_sum (fun q hq =>
      admissibleSupport_filter_card_le_valuation hn
        (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hq).1) hS)

/-- An arity deficit is already a finite supply of smooth shifted primes. -/
theorem smoothPrimePool_card_ge_arity_deficit (m n X y k : ℕ)
    (hn : 0 < n) (hφ : totient m=n) (hk : k ≤ m.primeFactors.card)
    (hX : ∀ p ∈ m.primeFactors, p ≤ X) :
    k-upperFactorMass n y ≤ (smoothPrimePool X y).card := by
  have hrough := admissibleSupport_rough_card_le_upperFactorMass n y hn m.primeFactors
    (primeFactors_mem_admissibleSupports hn hφ)
  have hsum := Finset.card_filter_add_card_filter_not
    (s := m.primeFactors) (p := fun p => p-1 ∈ Nat.smoothNumbers y)
  have hsmooth : (m.primeFactors.filter (fun p => p-1 ∈ Nat.smoothNumbers y)).card ≤
      (smoothPrimePool X y).card := by
    apply Finset.card_le_card
    intro p hp
    obtain ⟨hp,hs⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr
      ⟨Nat.mem_primesBelow.mpr ⟨by have := hX p hp; omega,Nat.prime_of_mem_primeFactors hp⟩,hs⟩
  omega

/-- A profile-based extraction test. The missing arity surplus and the entire
small-prime divisor cost are retained as hypotheses. -/
theorem exists_divisor_large_g_of_prime_profile
    (C s : ℝ) (hC : 0 ≤ C) (F : Finset ℕ) (n r k y : ℕ)
    (hn : 0 < n) (hr : 1 ≤ r) (hE : upperFactorMass n y ≤ k)
    (hF : ∀ m ∈ F, Squarefree m ∧ totient m=n ∧ k ≤ m.primeFactors.card)
    (hprofile : C^r*(n : ℝ)^s*(lowerDivisorCost n y : ℝ)^(r-1) <
      (F.card : ℝ)*(r : ℝ)^(k-upperFactorMass n y)) :
    ∃ d ∈ n.divisors, C*(d : ℝ)^s < (g d : ℝ) := by
  apply exists_divisor_large_g_of_exact_coloring C s hC F n r k hn hr hF
  have hr0 : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have ht : (tau r n : ℝ) ≤ (lowerDivisorCost n y : ℝ)^(r-1)*
      (r : ℝ)^(upperFactorMass n y) := by
    exact_mod_cast tau_le_split_prime_profile r n y hr hn
  calc
    _ ≤ C^r*(n : ℝ)^s*((lowerDivisorCost n y : ℝ)^(r-1)*
        (r : ℝ)^(upperFactorMass n y)) :=
      mul_le_mul_of_nonneg_left ht (by positivity)
    _ = (C^r*(n : ℝ)^s*(lowerDivisorCost n y : ℝ)^(r-1))*
        (r : ℝ)^(upperFactorMass n y) := by ring
    _ < ((F.card : ℝ)*(r : ℝ)^(k-upperFactorMass n y))*
        (r : ℝ)^(upperFactorMass n y) :=
      mul_lt_mul_of_pos_right hprofile (pow_pos hr0 _)
    _ = _ := by rw [mul_assoc,← pow_add,Nat.sub_add_cancel hE]

end Erdos821
