import Submission.UniformScaleError

/-! # Uniform wide-pair incidence counts at fixed enlarged cutoffs -/
open Nat Finset Filter
open scoped Classical BigOperators Topology
namespace Erdos821
open AnalyticSieve
set_option maxHeartbeats 3000000

lemma fixed_multiple_le_next_exponent (t K m : ℕ) (hm : K ≤ m) :
    K*independentN t m ≤ independentN (t+1) m := by
  have hK : K ≤ (2 : ℕ)^(64*m) := hm.trans (Nat.lt_two_pow_self.le.trans
    (Nat.pow_le_pow_right (by decide) (by omega)))
  have h := Nat.mul_le_mul_right (independentN t m) hK
  convert h using 1
  simp only [independentN,← pow_add]
  congr 1
  ring

lemma widePair_prime_divisor_card_le_enlarged (a m n : ℕ) (ha : 22 ≤ a) (hm : 1 ≤ m) (hn : 0<n)
    (hN : n < independentN (widePairScale a+1) m) :
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
  have hbig : independentN (widePairScale a+1) m<(independentN a m)^5 := by
    simp only [independentN,← pow_mul,widePairScale]
    apply Nat.pow_lt_pow_right (by decide)
    have hh := Nat.mul_lt_mul_of_pos_right (by omega : 4*a+20+1<5*a) hm
    nlinarith only [hh]
  exact (not_lt_of_ge (hp5.trans (hlow.trans hprod))) (hN.trans hbig)

lemma widePair_divisor_incidence_le_enlarged (a m n : ℕ) (ha : 22 ≤ a) (hm : 1 ≤ m) (hn : 0<n)
    (hN : n < independentN (widePairScale a+1) m) :
    ((widePairPool a m).filter (fun d => d ∣ n)).card ≤ 16 := by
  let S := (widePairLeft a m ∪ widePairRight a m).filter (fun p => p ∣ n)
  have hS : S.card ≤ 4 := widePair_prime_divisor_card_le_enlarged a m n ha hm hn hN
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
