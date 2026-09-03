import Submission.SubsetProductMass
import Submission.RoughModulusMean
import Submission.QuantitativeShiftedMoments

/-!
# Arbitrary prime-subset modulus pools

The reciprocal-totient mass is an elementary symmetric sum. Their
incidences in shifted primes are controlled by the appropriate binomial
term in a higher divisor function.
-/
open Nat Finset ArithmeticFunction Filter
open scoped Classical BigOperators
namespace Erdos821
open AnalyticSieve HigherDivisors
set_option maxHeartbeats 3000000

noncomputable def primeSubsetModuli (P : Finset ℕ) (r : ℕ) : Finset ℕ :=
  (P.powersetCard r).image (fun S => ∏ p ∈ S, p)

lemma prime_subset_product_inj (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (r : ℕ) :
    Set.InjOn (fun S : Finset ℕ => ∏ p ∈ S, p) (↑(P.powersetCard r) : Set (Finset ℕ)) := by
  intro S hS T hT he
  have hSP := (mem_powersetCard.mp hS).1
  have hTP := (mem_powersetCard.mp hT).1
  have h := congrArg Nat.primeFactors he
  simpa only [Nat.primeFactors_prod (fun p hp => hP p (hSP hp)),
    Nat.primeFactors_prod (fun p hp => hP p (hTP hp))] using h

lemma primeSubsetModuli_pos (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    {r d : ℕ} (hd : d ∈ primeSubsetModuli P r) : 0 < d := by
  obtain ⟨S,hS,rfl⟩ := mem_image.mp hd
  exact prod_pos (fun p hp => (hP p ((mem_powersetCard.mp hS).1 hp)).pos)

lemma primeSubsetModuli_le (P : Finset ℕ) (H : ℕ) (hH : ∀ p ∈ P, p ≤ H)
    {r d : ℕ} (hd : d ∈ primeSubsetModuli P r) : d ≤ H^r := by
  obtain ⟨S,hS,rfl⟩ := mem_image.mp hd
  calc
    _ ≤ ∏ _p ∈ S, H := prod_le_prod' (fun p hp => hH p ((mem_powersetCard.mp hS).1 hp))
    _ = _ := by rw [prod_const,(mem_powersetCard.mp hS).2]

lemma primeSubsetModuli_rough (P : Finset ℕ) (L : ℕ)
    (hP : ∀ p ∈ P, p.Prime ∧ L ≤ p)
    {r d : ℕ} (hd : d ∈ primeSubsetModuli P r) {c : ℕ}
    (hc : c ∈ d.divisors.erase 1) : L ≤ c := by
  obtain ⟨hc1,hcd⟩ := mem_erase.mp hc
  have hcd' := Nat.dvd_of_mem_divisors hcd
  have hd0 := primeSubsetModuli_pos P (fun p hp => (hP p hp).1) hd
  obtain ⟨q,hq,hqc⟩ := Nat.exists_prime_and_dvd hc1
  have hqD := hq.mem_primeFactors (hqc.trans hcd') hd0.ne'
  obtain ⟨S,hS,rfl⟩ := mem_image.mp hd
  have hSP := (mem_powersetCard.mp hS).1
  rw [Nat.primeFactors_prod (fun p hp => (hP p (hSP hp)).1)] at hqD
  exact (hP q (hSP hqD)).2.trans (Nat.le_of_dvd (Nat.pos_of_mem_divisors hcd) hqc)

lemma primeSubsetModuli_mass (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (r : ℕ) :
    poolTotientMass (primeSubsetModuli P r) =
      elementaryMass P (fun p => (p.totient : ℝ)⁻¹) r := by
  unfold poolTotientMass primeSubsetModuli elementaryMass
  rw [sum_image (prime_subset_product_inj P hP r)]
  apply sum_congr rfl
  intro S hS
  have hprime : ∀ p ∈ S, p.Prime := fun p hp => hP p ((mem_powersetCard.mp hS).1 hp)
  rw [totient_prod_primes S hprime,Nat.cast_prod,prod_inv_distrib]
  congr 1
  apply prod_congr rfl
  intro p hp
  rw [Nat.totient_prime (hprime p hp)]

lemma primeSubsetModuli_divisor_count (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (r n : ℕ) (_hn : 0 < n) :
    ((primeSubsetModuli P r).filter (fun d => d ∣ n)).card =
      (P.filter (fun p => p ∣ n)).card.choose r := by
  have he : (P.powersetCard r).filter (fun S => (∏ p ∈ S, p) ∣ n) =
      (P.filter (fun p => p ∣ n)).powersetCard r := by
    ext S
    simp only [mem_filter,mem_powersetCard]
    constructor
    · rintro ⟨⟨hSP,hSr⟩,hprod⟩
      exact ⟨fun p hp => mem_filter.mpr ⟨hSP hp,(dvd_prod_of_mem _root_.id hp).trans hprod⟩,hSr⟩
    · rintro ⟨hSP,hSr⟩
      have hsub : S ⊆ P := fun p hp => (mem_filter.mp (hSP hp)).1
      exact ⟨⟨hsub,hSr⟩,(Sieve.prod_primes_dvd_iff S (fun p hp => hP p (hsub hp)) n).mpr
        (fun p hp => (mem_filter.mp (hSP hp)).2)⟩
  unfold primeSubsetModuli
  rw [filter_image,he,Finset.card_image_of_injOn
    (prime_subset_product_inj (P.filter (fun p => p ∣ n))
      (fun p hp => hP p (mem_filter.mp hp).1) r),card_powersetCard]

lemma binomial_term_le_power (k r a : ℕ) : k^r*a.choose r ≤ (k+1)^a := by
  by_cases hra : r ≤ a
  · rw [add_pow]
    have h := single_le_sum (f := fun i : ℕ => k^i*1^(a-i)*a.choose i)
      (fun i _ => Nat.zero_le _) (mem_range.mpr (Nat.lt_succ_of_le hra))
    simpa only [one_pow,mul_one,Nat.cast_id] using h
  · simp only [Nat.choose_eq_zero_of_lt (by omega : a < r),mul_zero,Nat.zero_le]

lemma primeSubsetModuli_weighted_incidence_le_tau (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (k r n : ℕ) (hn : 0 < n) :
    k^r*((primeSubsetModuli P r).filter (fun d => d ∣ n)).card ≤ tau (k+1) n := by
  rw [primeSubsetModuli_divisor_count P hP r n hn]
  have hsub : P.filter (fun p => p ∣ n) ⊆ n.primeFactors := by
    intro p hp
    obtain ⟨hp,hpn⟩ := mem_filter.mp hp
    exact (hP p hp).mem_primeFactors hpn hn.ne'
  exact (Nat.mul_le_mul_left _ (Nat.choose_le_choose r (card_le_card hsub))).trans
    ((binomial_term_le_power k r n.primeFactors.card).trans
      (pow_primeFactors_card_le_tau k n hn.ne'))

/-- Proper prime powers are retained as an explicit error term. -/
theorem primeSubsetModuli_progression_le_moment (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (k r Q N : ℕ) (hN : 1 ≤ N)
    (hcard : (primeSubsetModuli P r).card ≤ Q) :
    (k : ℝ)^r*(∑ d ∈ primeSubsetModuli P r, residueOneMangoldt d N) ≤
      primeLogDivisorMoment (k+1) N+(k : ℝ)^r*(2*(Q : ℝ)*Real.sqrt N*Real.log N) := by
  let M := primeSubsetModuli P r
  let I (n : ℕ) := (M.filter (fun d => d ∣ n-1)).card
  have hpoint (n : ℕ) (hn : n ∈ Icc 1 N) :
      (k : ℝ)^r*((I n : ℝ)*vonMangoldt n) ≤
        (if n.Prime then Real.log (n : ℝ)*(tau (k+1) (n-1) : ℝ) else 0)+
        (if ¬n.Prime then (k : ℝ)^r*(Q : ℝ)*vonMangoldt n else 0) := by
    by_cases hp : n.Prime
    · rw [if_pos hp,if_neg (not_not.mpr hp),add_zero,vonMangoldt_apply_prime hp]
      have hi : (k : ℝ)^r*(I n : ℝ) ≤ tau (k+1) (n-1) := by
        exact_mod_cast primeSubsetModuli_weighted_incidence_le_tau P hP k r (n-1)
          (by have := hp.two_le; omega)
      have h := mul_le_mul_of_nonneg_right hi (Real.log_natCast_nonneg n)
      nlinarith only [h]
    · rw [if_neg hp,if_pos hp,zero_add]
      have hi : (I n : ℝ) ≤ Q := by exact_mod_cast (card_filter_le M _).trans hcard
      have h := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hi
        (vonMangoldt_nonneg (n := n))) (pow_nonneg (Nat.cast_nonneg k) r)
      simpa only [mul_assoc] using h
  have hpr : (Icc 1 N).filter Nat.Prime = (N+1).primesBelow := by
    ext p
    simp only [mem_filter,mem_Icc,Nat.mem_primesBelow]
    constructor
    · rintro ⟨⟨_,hpN⟩,hp⟩
      exact ⟨by omega,hp⟩
    · rintro ⟨hpN,hp⟩
      exact ⟨⟨hp.pos,by omega⟩,hp⟩
  calc
    _ = ∑ n ∈ Icc 1 N, (k : ℝ)^r*((I n : ℝ)*vonMangoldt n) := by
      rw [sum_family_progressions_eq_incidence,mul_sum]
    _ ≤ ∑ n ∈ Icc 1 N,
        ((if n.Prime then Real.log (n : ℝ)*(tau (k+1) (n-1) : ℝ) else 0)+
        (if ¬n.Prime then (k : ℝ)^r*(Q : ℝ)*vonMangoldt n else 0)) := sum_le_sum hpoint
    _ = primeLogDivisorMoment (k+1) N+(k : ℝ)^r*(Q : ℝ)*
        ∑ n ∈ (Icc 1 N).filter (fun n => ¬n.Prime), vonMangoldt n := by
      rw [sum_add_distrib]
      simp only [← sum_filter,hpr,primeLogDivisorMoment,mul_sum]
    _ ≤ primeLogDivisorMoment (k+1) N+(k : ℝ)^r*(Q : ℝ)*(2*Real.sqrt N*Real.log N) :=
      _root_.add_le_add le_rfl (mul_le_mul_of_nonneg_left (mangoldt_nonprime_sum_le N hN) (by positivity))
    _ = _ := by ring

end Erdos821
