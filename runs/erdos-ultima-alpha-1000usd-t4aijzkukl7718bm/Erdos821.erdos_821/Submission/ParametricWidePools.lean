import Submission.FixedMassBlockDensity

/-!
# Parametric wide two-prime modulus pools

Adjacent logarithmic intervals give fixed reciprocal mass, and the
resulting moduli have bounded incidence below the ambient prime scale.
-/
open Nat Finset Filter
open scoped Classical BigOperators
namespace Erdos821
open AnalyticSieve HigherDivisors
set_option maxHeartbeats 3000000

noncomputable def widePairLeft (a m : ℕ) := widePrimePool a (a+1) m
noncomputable def widePairRight (a m : ℕ) := widePrimePool (a+1) (a+2) m
noncomputable def widePairPool (a m : ℕ) := pairPrimeProducts (widePairLeft a m) (widePairRight a m)
def widePairMassDenom (a : ℕ) : ℕ := (2048*(a+1))*(2048*(a+2))
def widePairScale (a : ℕ) : ℕ := 4*a+20

lemma widePairMassDenom_pos (a : ℕ) : 0<widePairMassDenom a := by
  unfold widePairMassDenom
  positivity

lemma widePairLeft_prime (a m p : ℕ) (hp : p ∈ widePairLeft a m) : p.Prime :=
  (mem_widePrimePool.mp hp).1
lemma widePairRight_prime (a m p : ℕ) (hp : p ∈ widePairRight a m) : p.Prime :=
  (mem_widePrimePool.mp hp).1
lemma widePairPools_disjoint (a m : ℕ) : Disjoint (widePairLeft a m) (widePairRight a m) :=
  widePrimePool_disjoint _ _ _ _

lemma widePairPool_mass_lower (a m : ℕ) (hm : 1 ≤ m) :
    1/(widePairMassDenom a : ℝ) ≤ poolTotientMass (widePairPool a m) := by
  rw [widePairPool,pairPrimeProducts_mass _ _ (widePairLeft_prime a m)
    (widePairRight_prime a m) (widePairPools_disjoint a m)]
  have hL := widePrimePool_mass_lower a (a+1) m (by omega) hm
  have hR := widePrimePool_mass_lower (a+1) (a+2) m (by omega) hm
  have h := mul_le_mul hL hR (by positivity) (poolTotientMass_nonneg _)
  apply le_trans (le_of_eq ?_) h
  simp only [widePairMassDenom,Nat.cast_mul,Nat.cast_ofNat,
    show a+1-a=1 by omega,show a+2-(a+1)=1 by omega,Nat.cast_one]
  ring

lemma widePairPools_bounds (a m p : ℕ) (hp : p ∈ widePairLeft a m ∨ p ∈ widePairRight a m) :
    2 ≤ p ∧ independentN a m ≤ p ∧ p ≤ independentN (a+2) m := by
  have he (b : ℕ) : independentN b m=progressionScaleN (b*m) := by
    simp only [independentN,progressionScaleN,mul_assoc]
  simp only [he]
  rcases hp with hp | hp
  · obtain ⟨hp,hl,hu⟩ := mem_widePrimePool.mp hp
    exact ⟨hp.two_le,hl,hu.trans (progressionScaleN_monotone
      (Nat.mul_le_mul_right m (by omega : a+1 ≤ a+2)))⟩
  · obtain ⟨hp,hl,hu⟩ := mem_widePrimePool.mp hp
    exact ⟨hp.two_le,(progressionScaleN_monotone
      (Nat.mul_le_mul_right m (Nat.le_succ a))).trans hl,hu⟩

lemma widePairPool_bounds (a m d : ℕ) (hd : d ∈ widePairPool a m) :
    2 ≤ d ∧ independentN (2*a) m ≤ d ∧ d ≤ independentN (2*a+4) m := by
  obtain ⟨⟨p,q⟩,hpq,rfl⟩ := mem_image.mp hd
  obtain ⟨hp,hq⟩ := mem_product.mp hpq
  have hpb := widePairPools_bounds a m p (Or.inl hp)
  have hqb := widePairPools_bounds a m q (Or.inr hq)
  have heq (b : ℕ) : independentN (2*b) m=independentN b m*independentN b m := by
    simp only [independentN,← pow_add]
    congr 1
    ring
  refine ⟨by dsimp; nlinarith only [hpb.1,hqb.1],?_,?_⟩
  · rw [heq]
    exact Nat.mul_le_mul hpb.2.1 hqb.2.1
  · rw [show 2*a+4=2*(a+2) by omega,heq]
    exact Nat.mul_le_mul hpb.2.2 hqb.2.2

lemma widePairPool_card_le (a m : ℕ) : (widePairPool a m).card ≤ independentN (2*a+4) m := by
  have hs : widePairPool a m ⊆ Icc 1 (independentN (2*a+4) m) := by
    intro d hd
    have h := widePairPool_bounds a m d hd
    exact mem_Icc.mpr ⟨by omega,h.2.2⟩
  exact (card_le_card hs).trans_eq (by simp)

lemma widePairPool_smooth_odd (a b m d : ℕ) (ha : 1 ≤ a) (hb : a+3 ≤ b)
    (hm : 1 ≤ m) (hd : d ∈ widePairPool a m) :
    d ∈ Nat.smoothNumbers (independentN b m) ∧ Odd d := by
  obtain ⟨⟨p,q⟩,hpq,rfl⟩ := mem_image.mp hd
  obtain ⟨hp,hq⟩ := mem_product.mp hpq
  have hpb := widePairPools_bounds a m p (Or.inl hp)
  have hqb := widePairPools_bounds a m q (Or.inr hq)
  have hY : independentN (a+2) m < independentN b m := by
    apply Nat.pow_lt_pow_right (by decide)
    exact Nat.mul_lt_mul_of_pos_right (Nat.mul_lt_mul_of_pos_left (by omega) (by decide)) hm
  have hD : 2 < independentN a m := by
    change 2^1<2^(64*a*m)
    apply Nat.pow_lt_pow_right (by decide)
    have ham := Nat.le_mul_of_pos_left m ha
    nlinarith only [ham,hm]
  have hps := Nat.mem_smoothNumbers_of_lt (by omega : 0<p) (hpb.2.2.trans_lt hY)
  have hqs := Nat.mem_smoothNumbers_of_lt (by omega : 0<q) (hqb.2.2.trans_lt hY)
  refine ⟨Nat.mul_mem_smoothNumbers hps hqs,?_⟩
  exact ((widePairLeft_prime a m p hp).odd_of_ne_two (by omega)).mul
    ((widePairRight_prime a m q hq).odd_of_ne_two (by omega))

lemma widePair_prime_divisor_card_le (a m n : ℕ) (ha : 21 ≤ a) (hm : 1 ≤ m) (hn : 0<n)
    (hN : n < independentN (widePairScale a) m) :
    (((widePairLeft a m ∪ widePairRight a m).filter (fun p => p ∣ n)).card) ≤ 4 := by
  let S := (widePairLeft a m ∪ widePairRight a m).filter (fun p => p ∣ n)
  have hs : S ⊆ n.primeFactors := by
    intro p hp
    obtain ⟨hp,hd⟩ := mem_filter.mp hp
    have hpr : p.Prime := by
      rcases mem_union.mp hp with hp | hp
      · exact widePairLeft_prime a m p hp
      · exact widePairRight_prime a m p hp
    exact Nat.mem_primeFactors.mpr ⟨hpr,hd,hn.ne'⟩
  have hprod : (∏ p ∈ S, p) ≤ n := Nat.le_of_dvd hn
    ((Finset.prod_dvd_prod_of_subset S n.primeFactors (fun p => p) hs).trans (Nat.prod_primeFactors_dvd n))
  have hlow : (independentN a m)^S.card ≤ ∏ p ∈ S, p := by
    rw [← prod_const]
    exact Finset.prod_le_prod' (fun p hp =>
      (widePairPools_bounds a m p (mem_union.mp (mem_filter.mp hp).1)).2.1)
  by_contra hc
  have hc5 : 5 ≤ S.card := by change ¬S.card ≤ 4 at hc; omega
  have hp5 := Nat.pow_le_pow_right (by unfold independentN; positivity : 0 < independentN a m) hc5
  have hbig : independentN (widePairScale a) m<(independentN a m)^5 := by
    simp only [independentN,← pow_mul,widePairScale]
    apply Nat.pow_lt_pow_right (by decide)
    have hh := Nat.mul_lt_mul_of_pos_right (by omega : 4*a+20<5*a) hm
    nlinarith only [hh]
  exact (not_lt_of_ge (hp5.trans (hlow.trans hprod))) (hN.trans hbig)

lemma widePair_divisor_incidence_le (a m n : ℕ) (ha : 21 ≤ a) (hm : 1 ≤ m) (hn : 0<n)
    (hN : n < independentN (widePairScale a) m) :
    ((widePairPool a m).filter (fun d => d ∣ n)).card ≤ 16 := by
  let S := (widePairLeft a m ∪ widePairRight a m).filter (fun p => p ∣ n)
  have hS : S.card ≤ 4 := widePair_prime_divisor_card_le a m n ha hm hn hN
  have hsub : (widePairPool a m).filter (fun d => d ∣ n) ⊆
      (S ×ˢ S).image (fun z => z.1*z.2) := by
    intro d hd
    obtain ⟨hd,hdn⟩ := mem_filter.mp hd
    obtain ⟨⟨p,q⟩,hpq,rfl⟩ := mem_image.mp hd
    obtain ⟨hp,hq⟩ := mem_product.mp hpq
    have hpS : p ∈ S := mem_filter.mpr ⟨mem_union_left _ hp,(dvd_mul_right p q).trans hdn⟩
    have hqS : q ∈ S := mem_filter.mpr ⟨mem_union_right _ hq,(dvd_mul_left q p).trans hdn⟩
    exact mem_image.mpr ⟨(p,q),mem_product.mpr ⟨hpS,hqS⟩,rfl⟩
  exact (card_le_card hsub).trans (card_image_le.trans (by
    rw [card_product]
    exact Nat.mul_le_mul hS hS))

end Erdos821
