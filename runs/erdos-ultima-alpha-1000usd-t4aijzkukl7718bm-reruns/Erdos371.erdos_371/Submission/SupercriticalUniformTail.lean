import FormalConjecturesUtil
import Submission.SupercriticalMultiplicityTail
import Submission.PrimeLogBands
import Submission.PrimeDivisorSecondMoment

/-! Uniform, summable dyadic tails for supercritical prime-pair multiplicity.
These estimates are unsigned and do not settle the orientation conjecture. -/

namespace Erdos371SupercriticalUniformTail

open Finset Filter Erdos371PrimeDiscrepancy Erdos371SupercriticalPrimePairs
open Erdos371SupercriticalMultiplicityTail Erdos371PrimeLogBands
open Erdos371PrimeDivisorSecondMoment Erdos371SmallPrimeAveraging

noncomputable def factorNeighbors (s : Finset ℕ) (K N : ℕ) : Finset ℕ :=
  badFactors s K N ∪ (badFactors s K N).image (fun m => m-1)

lemma factorNeighbors_card (s : Finset ℕ) (K N : ℕ) :
    (factorNeighbors s K N).card ≤ 2*(badFactors s K N).card := by
  have hu := card_union_le (badFactors s K N) ((badFactors s K N).image (fun m => m-1))
  have hi := card_image_le (s := badFactors s K N) (f := fun m => m-1)
  unfold factorNeighbors
  omega

lemma multiplicity_zero : Erdos371SupercriticalPrimePairs.multiplicity 0=0 := by decide +kernel
lemma multiplicity_one : Erdos371SupercriticalPrimePairs.multiplicity 1=0 := by decide +kernel

lemma multiplicity_pos_input {n K : ℕ} (hK : 0<K) (hm : K≤Erdos371SupercriticalPrimePairs.multiplicity n) : 1<n := by
  by_contra h
  have hn : n=0 ∨ n=1 := by omega
  rcases hn with rfl | rfl <;> simp only [multiplicity_zero,multiplicity_one] at hm <;> omega

lemma mem_factorNeighbors {n K N : ℕ} {s : Finset ℕ}
    (hK : 0<K) (hnN : n<N) (hm : K≤Erdos371SupercriticalPrimePairs.multiplicity n)
    (hs : ∀ q, q.Prime → q≤N → n+1<winner n*q → q∈s) :
    n ∈ factorNeighbors s K N := by
  have hn := multiplicity_pos_input hK hm
  rcases lt_or_gt_of_ne (consecutive_ne n).symm with hup | hdown
  · have hc : K≤(n.primeFactors.filter (fun q => n+1<q*P (n+1))).card := by
      simpa [Erdos371SupercriticalPrimePairs.multiplicity,pairs_of_ascent hn hup] using hm
    have hsub : n.primeFactors.filter (fun q => n+1<q*P (n+1)) ⊆
        s.filter (fun q => q∣n) := by
      intro q hq
      obtain ⟨hqn,hprod⟩ := mem_filter.mp hq
      have hp := Nat.prime_of_mem_primeFactors hqn
      have hd := Nat.dvd_of_mem_primeFactors hqn
      have hqN : q≤N := (Nat.le_of_dvd (by omega) hd).trans hnN.le
      have hw : winner n=P (n+1) := max_eq_right hup.le
      exact mem_filter.mpr ⟨hs q hp hqN (by simpa [hw,Nat.mul_comm] using hprod),hd⟩
    apply mem_union_left
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega,hnN.le⟩,hc.trans (card_le_card hsub)⟩
  · have hc : K≤((n+1).primeFactors.filter (fun q => n+1<P n*q)).card := by
      simpa [Erdos371SupercriticalPrimePairs.multiplicity,pairs_of_descent hn hdown] using hm
    have hsub : (n+1).primeFactors.filter (fun q => n+1<P n*q) ⊆
        s.filter (fun q => q∣n+1) := by
      intro q hq
      obtain ⟨hqn,hprod⟩ := mem_filter.mp hq
      have hp := Nat.prime_of_mem_primeFactors hqn
      have hd := Nat.dvd_of_mem_primeFactors hqn
      have hqN : q≤N := (Nat.le_of_dvd (by omega) hd).trans (by omega)
      have hw : winner n=P n := max_eq_left hdown.le
      exact mem_filter.mpr ⟨hs q hp hqN (by simpa [hw] using hprod),hd⟩
    apply mem_union_right
    exact mem_image.mpr ⟨n+1,mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega,by omega⟩,
      hc.trans (card_le_card hsub)⟩,by omega⟩

lemma factorNeighbors_bound {s : Finset ℕ} (hs : ∀ p∈s,p.Prime) {k : ℕ}
    (hM : mass s≤8*(k+1:ℕ)) (N : ℕ) :
    ((factorNeighbors s (2^k) N).card:ℝ) ≤
      144*(N:ℝ)*(k+1:ℕ)^2/(2:ℝ)^(2*k) := by
  have hc : ((factorNeighbors s (2^k) N).card:ℝ) ≤ 2*(badFactors s (2^k) N).card := by
    exact_mod_cast factorNeighbors_card s (2^k) N
  have hb := badFactors_card_bound s hs (by positivity : 0<2^k) N
  have hden : (((2^k:ℕ):ℝ))^2=(2:ℝ)^(2*k) := by
    push_cast
    rw [← pow_mul]
    congr 1
    omega
  rw [hden] at hb
  have hm0 := Erdos371PrimeDeletionVariance.mass_nonneg s
  have hkk : (1:ℝ)≤(k+1:ℕ) := by exact_mod_cast (show 1≤k+1 by omega)
  have hmass : mass s^2+mass s≤72*(k+1:ℕ)^2 := by nlinarith
  have hh := mul_le_mul_of_nonneg_left hmass (Nat.cast_nonneg (α := ℝ) N)
  have hd := div_le_div_of_nonneg_right hh (by positivity : (0:ℝ)≤2^(2*k))
  calc
    _ ≤ (2:ℝ)*((badFactors s (2^k) N).card:ℝ) := hc
    _ ≤ 2*((N:ℝ)*(72*(k+1:ℕ)^2)/(2:ℝ)^(2*k)) :=
      mul_le_mul_of_nonneg_left (hb.trans hd) (by norm_num)
    _ = _ := by ring

lemma eight_mul_le_pow {k : ℕ} (hk : 2≤k) : 8*k≤2^(2*k) := by
  induction k,hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    have he : 2*(k+1)=2*k+2 := by omega
    rw [he,pow_add]
    norm_num
    nlinarith

lemma tail_parameters {k T : ℕ} (hk : 2≤k) (hT : 2^(2*k)≤T) :
    let W := 2^(2*k)
    let J := T/W
    let H := T-2*k
    let L := H-J
    0<J ∧ 0<L ∧ 2*k≤T ∧ L+J=H ∧ T≤2*L ∧
      (T+1-L)*W≤4*(k+1)*L ∧ T+1≤2^(2*k+1)*J := by
  dsimp only
  let W := 2^(2*k)
  let J := T/W
  let H := T-2*k
  let L := H-J
  have hW0 : 0<W := by dsimp [W]; positivity
  have hJ : 0<J := Nat.div_pos hT hW0
  have h8k : 8*k≤W := eight_mul_le_pow hk
  have hW4 : 4≤W := by omega
  have hJW : J*W≤T := Nat.div_mul_le_self T W
  have hrem : T<W*(J+1) := Nat.lt_mul_div_succ T hW0
  have hfourJ : 4*J≤T := by nlinarith
  have hsum : 2*(2*k+J)≤T := by nlinarith
  have hkT : 2*k≤T := by omega
  have hHe : H+2*k=T := Nat.sub_add_cancel hkT
  have hJL : J≤H := by dsimp [H]; omega
  have hLe : L+J=H := Nat.sub_add_cancel hJL
  have hhalf : T≤2*L := by omega
  have hL : 0<L := by omega
  have hw : T+1-L=2*k+J+1 := by omega
  have hwidth : (T+1-L)*W≤4*(k+1)*L := by
    rw [hw]
    have h1 := Nat.mul_le_mul_left (2*k+1) hT
    have h2 := Nat.mul_le_mul_left (2*k+2) hhalf
    change (2*k+1)*W≤(2*k+1)*T at h1
    nlinarith
  have hU : T+1≤2^(2*k+1)*J := by
    rw [pow_succ]
    change T+1≤W*2*J
    nlinarith
  exact ⟨hJ,hL,hkT,hLe,hhalf,hwidth,hU⟩

lemma prime_band_cover {q T : ℕ} (hq : q.Prime) (hsize : q≤2^T) :
    q∈band 1 (T+1) := by
  apply mem_band.mpr
  exact ⟨hq,by simpa using hq.two_le,
    hsize.trans_lt (Nat.pow_lt_pow_right (by omega : 1<2) (by omega : T<T+1))⟩

lemma global_tail_bound {k T : ℕ} (hT : T<2^(2*k)) :
    (tailCount (2^k) (2^T):ℝ) ≤ 144*(2:ℝ)^T*(k+1:ℕ)^2/(2:ℝ)^(2*k) := by
  have hM : mass (band 1 (T+1))≤8*(k+1:ℕ) := by
    have hh := band_mass_bound (L := 1) (U := T+1) (B := 2*k) (by omega)
      (by simpa using hT)
    change mass (band 1 (T+1))≤4*(2*k:ℕ) at hh
    push_cast at hh ⊢
    linarith
  have hsub : (range (2^T)).filter (fun n => 2^k≤Erdos371SupercriticalPrimePairs.multiplicity n) ⊆
      factorNeighbors (band 1 (T+1)) (2^k) (2^T) := by
    intro n hn
    obtain ⟨hn,hm⟩ := mem_filter.mp hn
    exact mem_factorNeighbors (by positivity) (mem_range.mp hn) hm
      (fun q hq hqN _ => prime_band_cover hq hqN)
  have hh : (tailCount (2^k) (2^T):ℝ)≤(factorNeighbors (band 1 (T+1)) (2^k) (2^T)).card := by
    exact_mod_cast card_le_card hsub
  exact hh.trans (by simpa using factorNeighbors_bound (fun p hp => band_primes hp) hM (2^T))

lemma refined_cover {K T H L J : ℕ} (hK : 0<K) (hHJ : L+J=H) :
    (tailCount (K) (2^T):ℝ) ≤ (2:ℝ)^H+
      (largeCover L T (2^T)).card+(factorNeighbors (band J (T+1)) (K) (2^T)).card := by
  have hsub : (range (2^T)).filter (fun n => K≤Erdos371SupercriticalPrimePairs.multiplicity n) ⊆
      (range (2^H) ∪ largeCover L T (2^T)) ∪ factorNeighbors (band J (T+1)) (K) (2^T) := by
    intro n hn
    obtain ⟨hnN,hm⟩ := mem_filter.mp hn
    have hnlt := mem_range.mp hnN
    by_cases hsmall : n<2^H
    · exact mem_union_left _ (mem_union_left _ (mem_range.mpr hsmall))
    · have hlo : 2^H≤n+1 := by omega
      have hn0 : 0<n := multiplicity_pos_input hK hm |>.trans' (by omega)
      by_cases hw : 2^L≤winner n
      · exact mem_union_left _ (mem_union_right _ (mem_largeCover hn0 hnlt hw))
      · apply mem_union_right
        apply mem_factorNeighbors hK hnlt hm
        intro q hq hqN hprod
        apply mem_band.mpr
        refine ⟨hq,?_,hqN.trans_lt (Nat.pow_lt_pow_right (by omega : 1<2) (by omega : T<T+1))⟩
        by_contra hqsmall
        have hmul : winner n*q≤2^L*2^J := Nat.mul_le_mul (by omega) (by omega)
        rw [← pow_add,hHJ] at hmul
        omega
  have hc := (card_le_card hsub).trans (card_union_le _ _)
  have hc' := card_union_le (range (2^H)) (largeCover L T (2^T))
  have hh : tailCount (K) (2^T)≤2^H+(largeCover L T (2^T)).card+
      (factorNeighbors (band J (T+1)) (K) (2^T)).card := by
    unfold tailCount
    simp only [card_range] at hc'
    omega
  exact_mod_cast hh

/-- Uniform in the interval size: the tail bound is summable over dyadic
multiplicity levels after multiplication by that level. -/
theorem dyadic_tail_bound {k : ℕ} (hk : 2≤k) (T : ℕ) :
    (tailCount (2^k) (2^T):ℝ) ≤ 256*(2:ℝ)^T*(k+1:ℕ)^2/(2:ℝ)^(2*k) := by
  by_cases hT : T<2^(2*k)
  · have hh := global_tail_bound (k := k) hT
    exact hh.trans (by gcongr; norm_num)
  · have hT' : 2^(2*k)≤T := by omega
    obtain ⟨hJ,hL,hkT,hHJ,hhalf,hwidth,hU⟩ := tail_parameters hk hT'
    let J := T/2^(2*k)
    let H := T-2*k
    let L := H-J
    have hcover := refined_cover (K := 2^k) (T := T) (by positivity) hHJ
    have hM : mass (band J (T+1))≤8*(k+1:ℕ) := by
      have hh := band_mass_bound hJ hU
      change mass (band J (T+1))≤4*(2*k+1:ℕ) at hh
      push_cast at hh ⊢
      linarith
    have hf := factorNeighbors_bound (fun p hp => band_primes hp) hM (2^T)
    have hl := largeCover_card hL T (2^T)
    have hLr : (0:ℝ)<L := by exact_mod_cast hL
    have hWr : (0:ℝ)<(2:ℝ)^(2*k) := by positivity
    have hw : ((T+1-L:ℕ):ℝ)/(L:ℝ)≤4*(k+1:ℕ)/(2:ℝ)^(2*k) := by
      apply (div_le_div_iff₀ hLr hWr).mpr
      exact_mod_cast hwidth
    have hlarge : ((largeCover L T (2^T)).card:ℝ)≤
        32*(2:ℝ)^T*(k+1:ℕ)/(2:ℝ)^(2*k) := by
      have hh := mul_le_mul_of_nonneg_left hw (by positivity : (0:ℝ)≤8*(2:ℝ)^T)
      push_cast at hl
      change ((largeCover L T (2^T)).card:ℝ)≤8*(2:ℝ)^T*(T+1-L:ℕ)/(L:ℝ) at hl
      calc
        _ ≤ 8*(2:ℝ)^T*(T+1-L:ℕ)/(L:ℝ) := hl
        _ = 8*(2:ℝ)^T*(((T+1-L:ℕ):ℝ)/(L:ℝ)) := by ring
        _ ≤ 8*(2:ℝ)^T*(4*(k+1:ℕ)/(2:ℝ)^(2*k)) := hh
        _ = _ := by ring
    have hsmall : (2:ℝ)^H=(2:ℝ)^T/(2:ℝ)^(2*k) := by
      have he : H+2*k=T := Nat.sub_add_cancel hkT
      apply (eq_div_iff hWr.ne').mpr
      rw [← pow_add,he]
    change (tailCount (2^k) (2^T):ℝ)≤(2:ℝ)^H+
      (largeCover L T (2^T)).card+(factorNeighbors (band J (T+1)) (2^k) (2^T)).card at hcover
    norm_num only [Nat.cast_pow,Nat.cast_ofNat] at hf
    rw [hsmall] at hcover
    have hkk : (1:ℝ)≤(k+1:ℕ) := by exact_mod_cast (show 1≤k+1 by omega)
    have hc : (1:ℝ)+32*(k+1:ℕ)+144*(k+1:ℕ)^2≤256*(k+1:ℕ)^2 := by nlinarith
    have hb : (tailCount (2^k) (2^T):ℝ) ≤
        (2:ℝ)^T/(2:ℝ)^(2*k)*(1+32*(k+1:ℕ)+144*(k+1:ℕ)^2) := by
      calc
        _ ≤ (2:ℝ)^T/(2:ℝ)^(2*k)+
            32*(2:ℝ)^T*(k+1:ℕ)/(2:ℝ)^(2*k)+
            144*(2:ℝ)^T*(k+1:ℕ)^2/(2:ℝ)^(2*k) :=
          hcover.trans (add_le_add (add_le_add le_rfl hlarge) hf)
        _ = _ := by ring
    calc
      _ ≤ _ := hb
      _ ≤ (2:ℝ)^T/(2:ℝ)^(2*k)*(256*(k+1:ℕ)^2) :=
        mul_le_mul_of_nonneg_left hc (by positivity)
      _ = _ := by ring


/-- A bound valid simultaneously for every counting range. -/
theorem uniform_tail_bound {k : ℕ} (hk : 2≤k) (N : ℕ) :
    (tailCount (2^k) N:ℝ)/(N:ℝ) ≤ 512*(k+1:ℕ)^2/(2:ℝ)^(2*k) := by
  by_cases hN : N=0
  · subst N
    simp only [Nat.cast_zero,div_zero]
    positivity
  have hn : 0<N := Nat.pos_of_ne_zero hN
  have hNr : (0:ℝ)<N := by exact_mod_cast hn
  let T := Nat.log 2 N+1
  have hnT : N<2^T := Nat.lt_pow_succ_log_self (by omega) N
  have hpow : (2:ℝ)^T≤2*(N:ℝ) := by
    have hh := Nat.pow_log_le_self 2 hN
    have hhi : 2^T≤2*N := by dsimp [T]; rw [pow_succ]; nlinarith
    exact_mod_cast hhi
  have hc : (tailCount (2^k) N:ℝ)≤tailCount (2^k) (2^T) := by
    exact_mod_cast tailCount_mono (2^k) hnT.le
  have hb := dyadic_tail_bound hk T
  have hs : (tailCount (2^k) N:ℝ)≤512*(N:ℝ)*(k+1:ℕ)^2/(2:ℝ)^(2*k) := by
    calc
      _ ≤ _ := hc.trans hb
      _ ≤ 256*(2*(N:ℝ))*(k+1:ℕ)^2/(2:ℝ)^(2*k) := by gcongr
      _ = _ := by ring
  apply (div_le_iff₀ hNr).mpr
  exact hs.trans_eq (by ring)

end Erdos371SupercriticalUniformTail

#print axioms Erdos371SupercriticalUniformTail.dyadic_tail_bound

#print axioms Erdos371SupercriticalUniformTail.uniform_tail_bound
