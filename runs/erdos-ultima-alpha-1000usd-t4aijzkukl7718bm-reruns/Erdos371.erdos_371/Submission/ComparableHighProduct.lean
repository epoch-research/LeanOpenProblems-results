import FormalConjecturesUtil
import Submission.SieveScaleBands
import Submission.ComparableLowProduct

/-! A uniform bound on the high-product part of comparable consecutive
  prime factors. This file does not establish an orientation asymptotic. -/

namespace Erdos371ComparableHighProduct

open Finset Filter Erdos371SieveScaleBands Erdos371SieveParameters Erdos371CofactorSieve
open Erdos371Cofactor
open scoped Topology

attribute [local instance] Classical.propDecidable

def closeAbove (M L : ℕ) : Set ℕ :=
  {n | 1<n ∧ max (P n) (P (n+1)) ≤ 2^L * min (P n) (P (n+1)) ∧ M*(n+1)<P n*P (n+1)}

lemma factor_cofactor_ratio {a b p q n C : ℕ} (ha : 0<a) (hb : 0<b)
    (hp : 0<p) (hq : 0<q) (hn : 0<n) (han : a*p=n) (hbn : b*q=n+1)
    (hr : max p q ≤ C*min p q) : max a b ≤ 2*C*min a b := by
  have hpcq : p ≤ C*q := (le_max_left _ _).trans (hr.trans (Nat.mul_le_mul_left C (min_le_right _ _)))
  have hqcp : q ≤ C*p := (le_max_right _ _).trans (hr.trans (Nat.mul_le_mul_left C (min_le_left _ _)))
  have hab : a ≤ C*b := by
    have hmul := Nat.mul_le_mul_left b hqcp
    apply Nat.le_of_mul_le_mul_left (c := p) _ hp
    nlinarith
  have hba : b ≤ 2*C*a := by
    have hmul := Nat.mul_le_mul_left (2*a) hpcq
    apply Nat.le_of_mul_le_mul_left (c := q) _ hq
    nlinarith
  by_cases h : a≤b
  · simpa [min_eq_left h, max_eq_right h] using hba
  · have hh : b≤a := by omega
    rw [min_eq_right hh, max_eq_left hh]
    nlinarith

lemma cofactor_product_small {a b p q n M : ℕ} (ha : 0<a) (hb : 0<b)
    (han : a*p=n) (hbn : b*q=n+1) (hprod : M*(n+1)<p*q) : a*b*M<n := by
  have hmul := Nat.mul_lt_mul_of_pos_left hprod (Nat.mul_pos ha hb)
  have he : (a*b)*(p*q) = n*(n+1) := by rw [show (a*b)*(p*q)=(a*p)*(b*q) by ring, han, hbn]
  rw [he] at hmul
  apply Nat.lt_of_mul_lt_mul_right (a := n+1) (b := a*b*M) (c := n)
  nlinarith

lemma index_add_pow_le_exponent (k : ℕ) : k+2^k ≤ exponent k := by
  have hd := index_le_depth k
  have hd0 := depth_pos k
  have hp := Nat.one_le_two_pow (n := k)
  have hh : k+1 ≤ 12*depth k := by omega
  have hm := Nat.mul_le_mul_right (2^k) hh
  unfold exponent
  nlinarith

lemma cutoff_fits_band {L K k j t : ℕ} (hLK : L+3≤K) (hKk : K≤k)
    (hj : j ∈ band k t) : 2 * (2^(L+2)*2^j) * cutoff k ≤ 2^t := by
  have hb := (Finset.mem_filter.mp hj).2.1
  have he := index_add_pow_le_exponent k
  have hexp : 1+(L+2)+j+2^k ≤ t := by omega
  calc
    _ = 2^(1+(L+2)+j+2^k) := by
      unfold cutoff
      simp only [pow_add, pow_one]
      ring
    _ ≤ _ := Nat.pow_le_pow_right (by decide) hexp

lemma factor_mem_cofactorInputs {a b p q n N k : ℕ} (ha : 0<a) (hb : 0<b)
    (hp : p.Prime) (hq : q.Prime) (han : a*p=n) (hbn : b*q=n+1)
    (hnN : n<N) (hzp : cutoff k≤p) (hzq : cutoff k≤q) : n ∈ cofactorInputs k a b N := by
  have hpa : n/a=p := by rw [← han, Nat.mul_div_cancel_left p ha]
  have hqb : (n+1)/b=q := by rw [← hbn, Nat.mul_div_cancel_left q hb]
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_range.mpr hnN, ⟨p,han.symm⟩, ⟨q,hbn.symm⟩, ?_⟩
  simpa [hpa,hqb] using And.intro hp (And.intro hq (And.intro hzp hzq))

/-- On a dyadic input shell, the high-product comparisons lie in the
  summed sieve cover. -/
lemma mem_scaleCover {L K t n : ℕ} (hLK : L+3≤K)
    (hn : n ∈ closeAbove (threshold K) L) (hnN : n<2^t) (hlo : 2^t≤2*n) :
    n ∈ scaleCover K (2^(L+2)) t := by
  obtain ⟨hn1,hr,hprod⟩ := hn
  let a := cofactor n
  let b := cofactor (n+1)
  let p := P n
  let q := P (n+1)
  have ha : 0<a := cofactor_pos hn1
  have hb : 0<b := cofactor_pos (by omega : 1<n+1)
  have hp : p.Prime := Nat.prime_maxPrimeFac_of_one_lt n hn1
  have hq : q.Prime := Nat.prime_maxPrimeFac_of_one_lt (n+1) (by omega)
  have han : a*p=n := cofactor_mul n
  have hbn : b*q=n+1 := cofactor_mul (n+1)
  have hratio := factor_cofactor_ratio ha hb hp.pos hq.pos (by omega : 0<n) han hbn hr
  have hsmall := cofactor_product_small ha hb han hbn hprod
  let j := Nat.log 2 (min a b)
  have hm0 : min a b ≠ 0 := by omega
  have hA : 2^j ≤ min a b := Nat.pow_log_le_self 2 hm0
  have hmA : min a b<2^(j+1) := Nat.lt_pow_succ_log_self (by decide) (min a b)
  have hAa : 2^j ≤ a := hA.trans (min_le_left _ _)
  have hAb : 2^j ≤ b := hA.trans (min_le_right _ _)
  have hmax : max a b ≤ 2^(L+2)*2^j := by
    have hh := Nat.mul_le_mul_left (2*2^L) hmA.le
    have he : (2*2^L)*2^(j+1) = 2^(L+2)*2^j := by
      simp only [pow_add, pow_one]
      ring
    rw [he] at hh
    exact hratio.trans hh
  have haB : a ≤ 2^(L+2)*2^j := (le_max_left _ _).trans hmax
  have hbB : b ≤ 2^(L+2)*2^j := (le_max_right _ _).trans hmax
  have hKband : 2*j+exponent K ≤ t := by
    have hAA : 2^j*2^j ≤ a*b := Nat.mul_le_mul hAa hAb
    have hh := Nat.mul_le_mul_right (threshold K) hAA
    have hpow : 2^(2*j+exponent K) < (2:ℕ)^t := by
      calc
        _ = (2^j*2^j)*threshold K := by rw [threshold_eq_pow, pow_add, show 2*j=j+j by omega, pow_add]
        _ ≤ a*b*threshold K := hh
        _ < n := hsmall
        _ < 2^t := hnN
    exact ((Nat.pow_lt_pow_iff_right (by decide : 1<(2:ℕ))).mp hpow).le
  obtain ⟨k,hk,hj⟩ := exists_band hKband
  have hKk := (Finset.mem_Ico.mp hk).1
  have hz := (cutoff_fits_band hLK hKk hj).trans hlo
  have hzp : cutoff k≤p := by
    have hh := Nat.mul_le_mul_right (cutoff k) (Nat.mul_le_mul_left 2 haB)
    have hmul : a*cutoff k ≤ a*p := by nlinarith
    exact Nat.le_of_mul_le_mul_left hmul ha
  have hzq : cutoff k≤q := by
    have hh := Nat.mul_le_mul_right (cutoff k) (Nat.mul_le_mul_left 2 hbB)
    have hmul : b*cutoff k ≤ b*q := by nlinarith
    exact Nat.le_of_mul_le_mul_left hmul hb
  apply Finset.mem_biUnion.mpr
  refine ⟨k,hk,Finset.mem_biUnion.mpr ⟨j,hj,?_⟩⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨a,Finset.mem_Icc.mpr ⟨hAa,haB⟩,Finset.mem_biUnion.mpr ?_⟩
  refine ⟨b,Finset.mem_Icc.mpr ⟨hAb,hbB⟩, ?_⟩
  exact factor_mem_cofactorInputs ha hb hp hq han hbn hnN hzp hzq

noncomputable def shell (K L t : ℕ) : Finset ℕ :=
  (Finset.range (2^t)).filter fun n => 2^t≤2*n ∧ n ∈ closeAbove (threshold K) L

lemma shell_card_bound {K L : ℕ} (hLK : L+3≤K) (t : ℕ) :
    (shell K L t).card ≤
      12*(Real.exp 1)^2*((2^(L+2):ℕ):ℝ)^2*(2:ℝ)^t * tail K := by
  have hsub : shell K L t ⊆ scaleCover K (2^(L+2)) t := by
    intro n hn
    obtain ⟨hnN,hlo,hclose⟩ := Finset.mem_filter.mp hn
    exact mem_scaleCover hLK hclose (Finset.mem_range.mp hnN) hlo
  exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans (scaleCover_card_bound K (2^(L+2)) t)

noncomputable def aboveCount (K L N : ℕ) : Finset ℕ :=
  (Finset.range N).filter fun n => n ∈ closeAbove (threshold K) L

lemma aboveCount_mono (K L : ℕ) {N M : ℕ} (hNM : N≤M) :
    aboveCount K L N ⊆ aboveCount K L M := by
  intro n hn
  obtain ⟨hnN,h⟩ := Finset.mem_filter.mp hn
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ((Finset.mem_range.mp hnN).trans_le hNM),h⟩

lemma aboveCount_power_bound {K L : ℕ} (hLK : L+3≤K) (t : ℕ) :
    (aboveCount K L (2^t)).card ≤
      24*(Real.exp 1)^2*((2^(L+2):ℕ):ℝ)^2*(2:ℝ)^t * tail K := by
  induction t with
  | zero =>
    have he : aboveCount K L (2^0) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro n hn
      obtain ⟨hnN,hclose⟩ := Finset.mem_filter.mp hn
      have hnlt := Finset.mem_range.mp hnN
      have hn1 : 1<n := hclose.1
      norm_num at hnlt
      omega
    rw [he, Finset.card_empty, Nat.cast_zero]
    exact mul_nonneg (by positivity) (tail_nonneg K)
  | succ t ih =>
    have hsub : aboveCount K L (2^(t+1)) ⊆
        aboveCount K L (2^t) ∪ shell K L (t+1) := by
      intro n hn
      obtain ⟨hnN,hclose⟩ := Finset.mem_filter.mp hn
      by_cases hlow : n<2^t
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hlow,hclose⟩)
      · apply Finset.mem_union_right
        apply Finset.mem_filter.mpr
        refine ⟨hnN,?_,hclose⟩
        rw [pow_succ]
        omega
    have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    have hcast : ((aboveCount K L (2^(t+1))).card:ℝ) ≤
        (aboveCount K L (2^t)).card + (shell K L (t+1)).card := by exact_mod_cast hc
    have hs := shell_card_bound hLK (t+1)
    rw [pow_succ (2:ℝ) t] at hs ⊢
    nlinarith

lemma aboveCount_bound {K L : ℕ} (hLK : L+3≤K) {N : ℕ} (hN : 0<N) :
    (aboveCount K L N).card ≤
      48*(Real.exp 1)^2*((2^(L+2):ℕ):ℝ)^2*(N:ℝ) * tail K := by
  let t := Nat.log 2 N+1
  have hNt : N<2^t := Nat.lt_pow_succ_log_self (by decide) N
  have htwo : (2:ℕ)^t ≤ 2*N := by
    have h := Nat.pow_log_le_self 2 hN.ne'
    dsimp [t]
    rw [pow_succ]
    omega
  have htwo' : (2:ℝ)^t ≤ 2*N := by exact_mod_cast htwo
  have hc := (Nat.cast_le.mpr (Finset.card_le_card (aboveCount_mono K L hNt.le))).trans
    (aboveCount_power_bound hLK t)
  have hmul := mul_le_mul_of_nonneg_left htwo'
    (show 0 ≤ 24*(Real.exp 1)^2*((2^(L+2):ℕ):ℝ)^2*tail K from
      mul_nonneg (by positivity) (tail_nonneg K))
  nlinarith

/-- The high-product part has uniformly small upper density as the product
  multiplier tends through the sieve thresholds to infinity. -/
theorem closeAbove_partialDensity_bound {K L : ℕ} (hLK : L+3≤K) {N : ℕ} (hN : 0<N) :
    (closeAbove (threshold K) L).partialDensity Set.univ N ≤
      48*(Real.exp 1)^2*((2^(L+2):ℕ):ℝ)^2 * tail K := by
  rw [Erdos371ReflectionRange.partialDensity_eq_filter_card]
  change ((aboveCount K L N).card:ℝ)/N ≤ _
  apply (div_le_iff₀ (Nat.cast_pos.mpr hN)).mpr
  have hh := aboveCount_bound hLK hN
  nlinarith

end Erdos371ComparableHighProduct

#print axioms Erdos371ComparableHighProduct.mem_scaleCover
#print axioms Erdos371ComparableHighProduct.shell_card_bound

#print axioms Erdos371ComparableHighProduct.closeAbove_partialDensity_bound
