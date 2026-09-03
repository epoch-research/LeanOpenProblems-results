import FormalConjecturesUtil
import Submission.ProductSignTransport

/-! A divisor bound for the fibers of the product sign transport.
This controls multiplicity but does not control its quadratic counting range. -/

namespace Erdos371ProductTransportFibers

open Finset Erdos371PrimeDiscrepancy Erdos371ProductSignTransport

lemma winner_gt_two {n : ℕ} (hn : 1<n) : 2<winner n := by
  have ha := (Nat.prime_maxPrimeFac_of_one_lt n hn).two_le
  have hb := (Nat.prime_maxPrimeFac_of_one_lt (n+1) (by omega)).two_le
  have hne := consecutive_ne n
  change 2≤P n at ha
  change 2≤P (n+1) at hb
  change 2 < max (P n) (P (n+1))
  omega

lemma lower_ne_of_opposite {n m p : ℕ} (hn : 1<n)
    (hnp : winner n=p) (hmp : winner m=p)
    (hup : P n<P (n+1)) (hdown : ¬P m<P (m+1)) : lower n≠lower m := by
  intro he
  simp only [lower,if_pos hup,if_neg hdown] at he
  have hpm : P m=p := by simpa [winner,max_eq_left (le_of_not_gt hdown)] using hmp
  have hpn : P (n+1)=p := by simpa [winner,max_eq_right hup.le] using hnp
  have hdm : p∣m := hpm ▸ Nat.maxPrimeFac_dvd
  have hdn : p∣m+2 := by
    have hd : p∣n+1 := hpn ▸ Nat.maxPrimeFac_dvd
    simpa [he,Nat.add_assoc] using hd
  have hd2 : p∣2 := (Nat.dvd_add_iff_right hdm).mpr hdn
  have hle := Nat.le_of_dvd (by norm_num : 0<(2:ℕ)) hd2
  have hgt : 2<p := hnp ▸ winner_gt_two hn
  omega

/-- On comparisons with a fixed winning prime, the losing endpoint determines
which comparison it came from, provided the input is at least two. -/
lemma lower_injective_fixed_winner {n m p : ℕ} (hn : 1<n) (hm : 1 < m)
    (hnp : winner n=p) (hmp : winner m=p) (he : lower n=lower m) : n=m := by
  by_cases h1 : P n<P (n+1)
  · by_cases h2 : P m<P (m+1)
    · simpa only [lower,if_pos h1,if_pos h2] using he
    · exact False.elim (lower_ne_of_opposite hn hnp hmp h1 h2 he)
  · by_cases h2 : P m<P (m+1)
    · exact False.elim (lower_ne_of_opposite hm hmp hnp h2 h1 he.symm)
    · simpa only [lower,if_neg h1,if_neg h2,Nat.add_right_cancel_iff] using he

def pairs (p N : ℕ) : Finset (ℕ×ℕ) :=
  ((range N).product (range N)).filter fun nm =>
    1<nm.1 ∧ 1<nm.2 ∧ winner nm.1=p ∧ winner nm.2=p

def productFiber (p N z : ℕ) : Finset (ℕ×ℕ) :=
  (pairs p N).filter fun nm => lower nm.1*lower nm.2=z

def fiber (p N t : ℕ) : Finset (ℕ×ℕ) :=
  (pairs p N).filter fun nm => transport nm.1 nm.2=t

lemma mem_pairs {p N : ℕ} {nm : ℕ×ℕ} (h : nm∈pairs p N) :
    nm.1<N ∧ nm.2<N ∧ 1<nm.1 ∧ 1<nm.2 ∧ winner nm.1=p ∧ winner nm.2=p := by
  obtain ⟨hr,hp⟩ := mem_filter.mp h
  obtain ⟨h1,h2⟩ := mem_product.mp hr
  exact ⟨mem_range.mp h1,mem_range.mp h2,hp⟩

lemma productFiber_card_le (p N z : ℕ) : (productFiber p N z).card≤z.divisors.card := by
  apply card_le_card_of_injOn (fun nm : ℕ×ℕ => lower nm.1)
  · intro nm hnm
    obtain ⟨hpair,hz⟩ := mem_filter.mp hnm
    have hm := mem_pairs hpair
    have hx := lower_bounds nm.1
    have hy := lower_bounds nm.2
    apply Nat.mem_divisors.mpr
    exact ⟨hz ▸ dvd_mul_right (lower nm.1) (lower nm.2),by nlinarith⟩
  · intro nm hnm ab hab he
    obtain ⟨hnp,hnz⟩ := mem_filter.mp hnm
    obtain ⟨hap,haz⟩ := mem_filter.mp hab
    have hn := mem_pairs hnp
    have ha := mem_pairs hap
    have hfirst : nm.1=ab.1 := lower_injective_fixed_winner
      hn.2.2.1 ha.2.2.1 hn.2.2.2.2.1 ha.2.2.2.2.1 he
    have hmul : lower nm.1*lower nm.2=lower nm.1*lower ab.2 := by
      simpa only [he] using hnz.trans haz.symm
    have hpos : 0<lower nm.1 := by have := lower_bounds nm.1; omega
    have hsecond : nm.2=ab.2 := lower_injective_fixed_winner
      hn.2.2.2.1 ha.2.2.2.1 hn.2.2.2.2.2 ha.2.2.2.2.2
      (Nat.mul_left_cancel hpos hmul)
    exact Prod.ext hfirst hsecond

/-- The product itself remains the losing endpoint of the new comparison,
even when the winning prime increases. -/
lemma lower_transport {n m : ℕ} (hn : 1<n) (hm : 1 < m)
    (hw : winner n=winner m) :
    lower (transport n m)=lower n*lower m := by
  have ht := (transport_sign_and_winner hn hm hw).1
  rw [sign_product_eq] at ht
  by_cases hs : sign n=sign m
  · rw [if_pos hs] at ht
    have hT : ¬P (transport n m)<P (transport n m+1) := by
      intro h
      simp [sign,h] at ht
    rw [lower,if_neg hT,transport,if_pos hs]
    have hx := lower_bounds n
    have hy := lower_bounds m
    have hprod : 1≤lower n*lower m := by nlinarith
    omega
  · rw [if_neg hs] at ht
    have hT : P (transport n m)<P (transport n m+1) := by
      by_contra h
      simp [sign,h] at ht
    rw [lower,if_pos hT,transport,if_neg hs]

lemma fiber_subset_losing_product (p N t : ℕ) :
    fiber p N t ⊆ productFiber p N (lower t) := by
  intro nm hnm
  obtain ⟨hp,ht⟩ := mem_filter.mp hnm
  have hn := mem_pairs hp
  have hl := lower_transport hn.2.2.1 hn.2.2.2.1
    (hn.2.2.2.2.1.trans hn.2.2.2.2.2.symm)
  rw [ht] at hl
  exact mem_filter.mpr ⟨hp,hl.symm⟩

/-- A sharper bound uses only the divisors of the output's losing endpoint. -/
theorem fiber_card_le_losing_divisors (p N t : ℕ) :
    (fiber p N t).card≤(lower t).divisors.card :=
  (card_le_card (fiber_subset_losing_product p N t)).trans
    (productFiber_card_le p N (lower t))

lemma fiber_subset_products (p N t : ℕ) :
    fiber p N t ⊆ productFiber p N t ∪ productFiber p N (t+1) := by
  intro nm hnm
  obtain ⟨hp,ht⟩ := mem_filter.mp hnm
  have hn := mem_pairs hp
  have hx := lower_bounds nm.1
  have hy := lower_bounds nm.2
  have hprod : 1<lower nm.1*lower nm.2 := by nlinarith
  by_cases hs : sign nm.1=sign nm.2
  · have he : lower nm.1*lower nm.2=t+1 := by
      simp only [transport,if_pos hs] at ht
      omega
    exact mem_union_right _ (mem_filter.mpr ⟨hp,he⟩)
  · have he : lower nm.1*lower nm.2=t := by simpa only [transport,if_neg hs] using ht
    exact mem_union_left _ (mem_filter.mpr ⟨hp,he⟩)

/-- The map is many-to-one, but at a fixed winner its fibers have a divisor bound. -/
theorem fiber_card_le (p N t : ℕ) :
    (fiber p N t).card≤t.divisors.card+(t+1).divisors.card := by
  exact ((card_le_card (fiber_subset_products p N t)).trans (card_union_le _ _)).trans
    (Nat.add_le_add (productFiber_card_le p N t) (productFiber_card_le p N (t+1)))


lemma lower_sign_injective {n m : ℕ} (hl : lower n=lower m) (hs : sign n=sign m) : n=m := by
  unfold lower at hl
  unfold sign at hs
  split_ifs at hl hs <;> omega

lemma sign_bool_injective {n m : ℕ}
    (hb : decide (sign n=1)=decide (sign m=1)) : sign n=sign m := by
  have hh := decide_eq_decide.mp hb
  unfold sign at hh ⊢
  split_ifs at hh ⊢ <;> simp_all

def allPairs (N : ℕ) : Finset (ℕ×ℕ) :=
  ((range N).product (range N)).filter fun nm =>
    1<nm.1 ∧ 1<nm.2 ∧ winner nm.1=winner nm.2

def allFiber (N t : ℕ) : Finset (ℕ×ℕ) :=
  (allPairs N).filter fun nm => transport nm.1 nm.2=t

lemma mem_allPairs {N : ℕ} {nm : ℕ×ℕ} (h : nm∈allPairs N) :
    nm.1<N ∧ nm.2<N ∧ 1<nm.1 ∧ 1<nm.2 ∧ winner nm.1=winner nm.2 := by
  obtain ⟨hr,hp⟩ := mem_filter.mp h
  obtain ⟨h1,h2⟩ := mem_product.mp hr
  exact ⟨mem_range.mp h1,mem_range.mp h2,hp⟩

lemma allFiber_product {N t : ℕ} {nm : ℕ×ℕ} (h : nm∈allFiber N t) :
    lower nm.1*lower nm.2=lower t := by
  obtain ⟨hp,ht⟩ := mem_filter.mp h
  have hn := mem_allPairs hp
  have he := lower_transport hn.2.2.1 hn.2.2.2.1 hn.2.2.2.2
  simpa only [ht] using he.symm

/-- Even after summing over all original winning primes, an output has at most
twice as many preimages as divisors of its losing endpoint. -/
theorem allFiber_card_le (N t : ℕ) :
    (allFiber N t).card≤2*(lower t).divisors.card := by
  let target := (lower t).divisors.product (univ : Finset Bool)
  have hcard : (allFiber N t).card≤target.card := by
    apply card_le_card_of_injOn (fun nm : ℕ×ℕ => (lower nm.1,decide (sign nm.1=1)))
    · intro nm hnm
      have hp := mem_allPairs (mem_filter.mp hnm).1
      have he := allFiber_product hnm
      have hx := lower_bounds nm.1
      have hy := lower_bounds nm.2
      refine mem_product.mpr ⟨Nat.mem_divisors.mpr ⟨?_,?_⟩,mem_univ _⟩
      · exact he ▸ dvd_mul_right (lower nm.1) (lower nm.2)
      · nlinarith
    · intro nm hnm ab hab he
      have hn := mem_allPairs (mem_filter.mp hnm).1
      have ha := mem_allPairs (mem_filter.mp hab).1
      have hprod1 := allFiber_product hnm
      have hprod2 := allFiber_product hab
      have hlow : lower nm.1=lower ab.1 := congrArg Prod.fst he
      have hsign : sign nm.1=sign ab.1 :=
        sign_bool_injective (congrArg Prod.snd he)
      have hfirst := lower_sign_injective hlow hsign
      have hmul : lower nm.1*lower nm.2=lower nm.1*lower ab.2 := by
        simpa only [hlow] using hprod1.trans hprod2.symm
      have hpos : 0<lower nm.1 := by have := lower_bounds nm.1; omega
      have hlow2 := Nat.mul_left_cancel hpos hmul
      have ht1 := (transport_sign_and_winner hn.2.2.1 hn.2.2.2.1 hn.2.2.2.2).1
      have ht2 := (transport_sign_and_winner ha.2.2.1 ha.2.2.2.1 ha.2.2.2.2).1
      rw [(mem_filter.mp hnm).2] at ht1
      rw [(mem_filter.mp hab).2] at ht2
      rw [hsign] at ht1
      have hsignprod : sign ab.1*sign nm.2=sign ab.1*sign ab.2 := by omega
      have hnz : sign ab.1≠0 := by unfold sign; split_ifs <;> norm_num
      have hsign2 : sign nm.2=sign ab.2 := mul_left_cancel₀ hnz hsignprod
      exact Prod.ext hfirst (lower_sign_injective hlow2 hsign2)
  simpa [target,Nat.mul_comm] using hcard

end Erdos371ProductTransportFibers

#print axioms Erdos371ProductTransportFibers.lower_injective_fixed_winner
#print axioms Erdos371ProductTransportFibers.lower_transport
#print axioms Erdos371ProductTransportFibers.fiber_card_le_losing_divisors
#print axioms Erdos371ProductTransportFibers.fiber_card_le

#print axioms Erdos371ProductTransportFibers.allFiber_card_le
