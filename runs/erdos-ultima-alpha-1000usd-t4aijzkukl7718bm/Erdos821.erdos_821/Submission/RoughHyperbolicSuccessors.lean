import Submission.ShortCofactorHyperbolicBound

/-!
# Nonsmooth predecessors mapped into the hyperbolic prime-pair sieve

The largest-factor witness is not assumed unique. A finite image cover is
sufficient for the upper bound, and the predecessor equality is retained.
-/
open Nat Finset ArithmeticFunction Filter
open scoped Classical BigOperators Topology
namespace Erdos821.AnalyticSieve
set_option maxHeartbeats 3000000

lemma rough_progression_card_le_hyperbolic (d Y X : ℕ) (hd : 0 < d)
    (hdY : d ∈ Nat.smoothNumbers Y) (hY : ¬Y.Prime) :
    (roughProgressionPrimes d Y X).card ≤
      (hyperbolicPrimePairPool d (X/d) Y (X/d)).card := by
  let P := hyperbolicPrimePairPool d (X/d) Y (X/d)
  let f : ℕ × ℕ → ℕ := fun x => d*x.1*x.2+1
  have hsub : roughProgressionPrimes d Y X ⊆ P.image f := by
    intro p hp
    obtain ⟨hpX,hddvd,hns⟩ := mem_filter.mp hp
    obtain ⟨hpX,hprime⟩ := Nat.mem_primesBelow.mp hpX
    have hpred : 0 < p-1 := Nat.sub_pos_of_lt hprime.one_lt
    have hnot : ¬∀ q, q.Prime → q ∣ p-1 → q<Y :=
      fun h => hns (Nat.mem_smoothNumbers'.mpr h)
    push_neg at hnot
    obtain ⟨q,hq,hqd,hYq⟩ := hnot
    have hYql : Y<q := lt_of_le_of_ne hYq (fun he => hY (he ▸ hq))
    let a := (p-1)/q
    have ha : 0 < a := Nat.div_pos (Nat.le_of_dvd hpred hqd) hq.pos
    have haeq : a*q=p-1 := Nat.div_mul_cancel hqd
    have hdq : d.Coprime q := by
      apply (hq.coprime_iff_not_dvd.mpr ?_).symm
      intro hqd'
      have hh := Nat.mem_smoothNumbers'.mp hdY q hq hqd'
      omega
    have hda : d ∣ a := hdq.dvd_of_dvd_mul_right (haeq ▸ hddvd)
    let k := a/d
    have hk : 0 < k := Nat.div_pos (Nat.le_of_dvd ha hda) hd
    have hkd : d*k=a := Nat.mul_div_cancel' hda
    have hmul : d*k*q=p-1 := by rw [hkd,haeq]
    have hprod : k*q ≤ X/d := by
      apply (Nat.le_div_iff_mul_le hd).mpr
      have he : k*q*d=d*k*q := by ring
      rw [he,hmul]
      omega
    have hkH : k ≤ X/d := (Nat.le_mul_of_pos_right k hq.pos).trans hprod
    have hqH : q ≤ X/d := (Nat.le_mul_of_pos_left q hk).trans hprod
    refine mem_image.mpr ⟨(k,q),?_,?_⟩
    · refine mem_filter.mpr ⟨mem_product.mpr ⟨mem_Icc.mpr ⟨hk,hkH⟩,
        mem_Icc.mpr ⟨hYql,hqH⟩⟩,hprod,hq,?_⟩
      have hp : d*k*q+1=p := by omega
      simpa only [hp] using hprime
    · dsimp [f]
      omega
  exact (card_le_card hsub).trans card_image_le

lemma hyperbolic_prime_pair_card_split (c H Y Z W : ℕ) :
    (hyperbolicPrimePairPool c H Y W).card ≤
      (hyperbolicPrimePairPool c H Y Z).card+(hyperbolicPrimePairPool c H Z W).card := by
  have hsub : hyperbolicPrimePairPool c H Y W ⊆
      hyperbolicPrimePairPool c H Y Z ∪ hyperbolicPrimePairPool c H Z W := by
    intro x hx
    obtain ⟨hxI,hprod,hprime,hsucc⟩ := mem_filter.mp hx
    obtain ⟨hxa,hxn⟩ := mem_product.mp hxI
    obtain ⟨hY,hW⟩ := mem_Icc.mp hxn
    by_cases hxZ : x.2 ≤ Z
    · exact mem_union_left _ (mem_filter.mpr ⟨mem_product.mpr
        ⟨hxa,mem_Icc.mpr ⟨hY,hxZ⟩⟩,hprod,hprime,hsucc⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨mem_product.mpr
        ⟨hxa,mem_Icc.mpr ⟨by omega,hW⟩⟩,hprod,hprime,hsucc⟩)
  exact (card_le_card hsub).trans (card_union_le _ _)

lemma rough_progression_card_le_long_short (d Y X Z : ℕ) (hd : 0 < d)
    (hdY : d ∈ Nat.smoothNumbers Y) (hY : ¬Y.Prime) :
    ((roughProgressionPrimes d Y X).card : ℝ) ≤
      ((hyperbolicPrimePairPool d (X/d) Y Z).card : ℝ)+
        ((hyperbolicPrimePairPool d (X/d) Z (X/d)).card : ℝ) := by
  exact_mod_cast (rough_progression_card_le_hyperbolic d Y X hd hdY hY).trans
    (hyperbolic_prime_pair_card_split d (X/d) Y Z (X/d))

end Erdos821.AnalyticSieve
