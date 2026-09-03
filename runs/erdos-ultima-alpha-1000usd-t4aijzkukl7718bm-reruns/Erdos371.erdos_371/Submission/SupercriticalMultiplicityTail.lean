import FormalConjecturesUtil
import Submission.SupercriticalPrimePairs
import Submission.PrimeHarmonicBlocks

/-! Quantitative bounds on the tail of the supercritical prime-pair
multiplicity. These are unsigned bounds, not orientation cancellation. -/

namespace Erdos371SupercriticalMultiplicityTail

open Finset Filter Erdos371PrimeDiscrepancy Erdos371SupercriticalPrimePairs
open Erdos371PrimeHarmonicBlocks

lemma pairs_of_ascent {n : ℕ} (hn : 1 < n) (hup : P n < P (n+1)) :
    pairs n = (n.primeFactors.filter (fun p => n+1 < p*P (n+1))).product {P (n+1)} := by
  ext z
  constructor
  · intro hz
    obtain ⟨hm,hprod⟩ := mem_filter.mp hz
    obtain ⟨hp,hq⟩ := mem_product.mp hm
    have hh := orientation (by omega : 0 < n) (Nat.prime_of_mem_primeFactors hp)
      (Nat.prime_of_mem_primeFactors hq) (Nat.dvd_of_mem_primeFactors hp)
      (Nat.dvd_of_mem_primeFactors hq) hprod
    have hlt := hh.2.mpr hup
    have he := hh.1
    rw [max_eq_right hlt.le,winner,max_eq_right hup.le] at he
    exact mem_product.mpr ⟨mem_filter.mpr ⟨hp,by simpa [he] using hprod⟩,
      mem_singleton.mpr he⟩
  · intro hz
    obtain ⟨hp,hq⟩ := mem_product.mp hz
    have he := mem_singleton.mp hq
    obtain ⟨hp,hprod⟩ := mem_filter.mp hp
    apply mem_filter.mpr
    refine ⟨mem_product.mpr ⟨hp,?_⟩,by simpa [he] using hprod⟩
    rw [he]
    exact Nat.mem_primeFactors.mpr ⟨Nat.prime_maxPrimeFac_of_one_lt (n+1) (by omega),
      Nat.maxPrimeFac_dvd,by omega⟩

lemma pairs_of_descent {n : ℕ} (hn : 1 < n) (hdown : P (n+1) < P n) :
    pairs n = ({P n} : Finset ℕ).product
      ((n+1).primeFactors.filter (fun q => n+1 < P n*q)) := by
  ext z
  constructor
  · intro hz
    obtain ⟨hm,hprod⟩ := mem_filter.mp hz
    obtain ⟨hp,hq⟩ := mem_product.mp hm
    have hh := orientation (by omega : 0 < n) (Nat.prime_of_mem_primeFactors hp)
      (Nat.prime_of_mem_primeFactors hq) (Nat.dvd_of_mem_primeFactors hp)
      (Nat.dvd_of_mem_primeFactors hq) hprod
    have hle : z.2 ≤ z.1 := by have := hh.2; omega
    have he := hh.1
    rw [max_eq_left hle,winner,max_eq_left hdown.le] at he
    exact mem_product.mpr ⟨mem_singleton.mpr he,
      mem_filter.mpr ⟨hq,by simpa [he] using hprod⟩⟩
  · intro hz
    obtain ⟨hp,hq⟩ := mem_product.mp hz
    have he := mem_singleton.mp hp
    obtain ⟨hq,hprod⟩ := mem_filter.mp hq
    apply mem_filter.mpr
    refine ⟨mem_product.mpr ⟨?_,hq⟩,by simpa [he] using hprod⟩
    rw [he]
    exact Nat.mem_primeFactors.mpr ⟨Nat.prime_maxPrimeFac_of_one_lt n hn,
      Nat.maxPrimeFac_dvd,by omega⟩

lemma power_bound_of_prime_subset {m B p K : ℕ} (hm : 0 < m) (hmB : m ≤ B)
    (hK : 0 < K) (S : Finset ℕ) (hS : S ⊆ m.primeFactors)
    (hcard : K ≤ S.card) (hprod : ∀ q ∈ S, B < p*q) :
    B^(K-1) < p^K := by
  obtain ⟨T,hTS,hTK⟩ := exists_subset_card_eq hcard
  have hT : T.Nonempty := card_pos.mp (by omega)
  have hdiv : (∏ q ∈ T, q) ∣ m :=
    (prod_dvd_prod_of_subset T m.primeFactors (fun q : ℕ => q)
      (hTS.trans hS)).trans (Nat.prod_primeFactors_dvd m)
  have hle : (∏ q ∈ T, q) ≤ B := (Nat.le_of_dvd hm hdiv).trans hmB
  have hh := prod_lt_prod_of_nonempty (s := T) (f := fun _ => B)
    (g := fun q => p*q) (fun _ _ => hm.trans_le hmB)
    (fun q hq => hprod q (hTS hq)) hT
  change (∏ _q ∈ T, B) < ∏ q ∈ T, p*q at hh
  rw [Finset.prod_mul_distrib] at hh
  simp only [Finset.prod_const,hTK] at hh
  have hbpow : B^K = B^(K-1)*B := by
    rw [← pow_succ]
    congr 1
    omega
  rw [hbpow] at hh
  exact Nat.lt_of_mul_lt_mul_right
    (hh.trans_le (Nat.mul_le_mul_left (p^K) hle))

/-- Many supercritical pairs force a largest prime very close to the input
size on the logarithmic scale. -/
theorem multiplicity_power_bound {n K : ℕ} (hn : 1 < n) (hK : 0 < K)
    (hm : K ≤ Erdos371SupercriticalPrimePairs.multiplicity n) :
    (n+1)^(K-1) < (winner n)^K := by
  rcases lt_or_gt_of_ne (consecutive_ne n).symm with hup | hdown
  · have hcard : K ≤ (n.primeFactors.filter (fun p => n+1 < p*P (n+1))).card := by
      simpa [Erdos371SupercriticalPrimePairs.multiplicity,pairs_of_ascent hn hup] using hm
    rw [winner,max_eq_right hup.le]
    exact power_bound_of_prime_subset (m := n) (by omega) (by omega) hK _
      (filter_subset _ _) hcard (fun q hq => by simpa [Nat.mul_comm] using (mem_filter.mp hq).2)
  · have hcard : K ≤ ((n+1).primeFactors.filter (fun q => n+1 < P n*q)).card := by
      simpa [Erdos371SupercriticalPrimePairs.multiplicity,pairs_of_descent hn hdown] using hm
    rw [winner,max_eq_left hdown.le]
    exact power_bound_of_prime_subset (m := n+1) (by omega) le_rfl hK _
      (filter_subset _ _) hcard (fun q hq => (mem_filter.mp hq).2)

lemma winner_lower_bound {n K H L : ℕ} (hn : 1 < n) (hK : 0 < K)
    (hm : K ≤ Erdos371SupercriticalPrimePairs.multiplicity n) (hH : 2^H ≤ n+1)
    (hLH : L*K ≤ H*(K-1)) :
    2^L ≤ winner n := by
  have hp := multiplicity_power_bound hn hK hm
  have hlo : (2^L)^K ≤ (n+1)^(K-1) := by
    rw [← pow_mul]
    exact (Nat.pow_le_pow_right (by omega : 0 < 2) hLH).trans
      (by simpa [pow_mul] using Nat.pow_le_pow_left hH (K-1))
  by_contra h
  have hhi := Nat.pow_le_pow_left (show winner n ≤ 2^L by omega) K
  omega


def primeCover (s : Finset ℕ) (N : ℕ) : Finset ℕ :=
  s.biUnion fun p => (Icc 1 (N/p)).image (fun a => a*p)

def neighborCover (s : Finset ℕ) (N : ℕ) : Finset ℕ :=
  primeCover s N ∪ (primeCover s N).image (fun m => m-1)

lemma primeCover_card (s : Finset ℕ) (N : ℕ) :
    (primeCover s N).card ≤ ∑ p ∈ s, N/p := by
  apply card_biUnion_le.trans
  apply sum_le_sum
  intro p hp
  simpa using (card_image_le (s := Icc 1 (N/p)) (f := fun a => a*p))

lemma neighborCover_card (s : Finset ℕ) (N : ℕ) :
    ((neighborCover s N).card : ℝ) ≤ 2*(N:ℝ)*(∑ p ∈ s, 1/(p:ℝ)) := by
  have hc : (neighborCover s N).card ≤ 2*(∑ p ∈ s, N/p) := by
    unfold neighborCover
    have hh := card_union_le (primeCover s N) ((primeCover s N).image (fun m => m-1))
    have hi := card_image_le (s := primeCover s N) (f := fun m => m-1)
    have hp := primeCover_card s N
    omega
  have hsum : (∑ p ∈ s, ((N/p : ℕ) : ℝ)) ≤ (N:ℝ)*(∑ p ∈ s, 1/(p:ℝ)) := by
    rw [mul_sum]
    exact sum_le_sum fun p hp => by simpa [div_eq_mul_inv] using (Nat.cast_div_le (m := N) (n := p) : ((N/p : ℕ):ℝ) ≤ (N:ℝ)/p)
  have hcR : ((neighborCover s N).card : ℝ) ≤ 2*(∑ p ∈ s, ((N/p : ℕ) : ℝ)) := by
    exact_mod_cast hc
  nlinarith

lemma mem_primeCover {s : Finset ℕ} {p m N : ℕ} (hp : p ∈ s) (hp0 : 0 < p)
    (hm : 0 < m) (hmN : m ≤ N) (hd : p ∣ m) : m ∈ primeCover s N := by
  apply mem_biUnion.mpr
  refine ⟨p,hp,mem_image.mpr ⟨m/p,mem_Icc.mpr ⟨?_,?_⟩,Nat.div_mul_cancel hd⟩⟩
  · exact Nat.div_pos (Nat.le_of_dvd hm hd) hp0
  · exact Nat.div_le_div_right hmN

lemma mem_neighborCover {s : Finset ℕ} {n N : ℕ} (hn : 0 < n) (hnN : n < N)
    (hp : winner n ∈ s) : n ∈ neighborCover s N := by
  have hprime := winner_prime hn
  by_cases hup : P n < P (n+1)
  · have hw : winner n = P (n+1) := max_eq_right hup.le
    have hd : winner n ∣ n+1 := by rw [hw]; exact Nat.maxPrimeFac_dvd
    have hh := mem_primeCover hp hprime.pos (by omega : 0 < n+1) (by omega : n+1 ≤ N) hd
    exact mem_union_right _ (mem_image.mpr ⟨n+1,hh,by omega⟩)
  · have hw : winner n = P n := max_eq_left (by omega)
    have hd : winner n ∣ n := by rw [hw]; exact Nat.maxPrimeFac_dvd
    exact mem_union_left _ (mem_primeCover hp hprime.pos hn hnN.le hd)

def largeCover (L T N : ℕ) : Finset ℕ :=
  (Icc L T).biUnion fun j => neighborCover (block j) N

lemma largeCover_card {L : ℕ} (hL : 0 < L) (T N : ℕ) :
    ((largeCover L T N).card : ℝ) ≤ 8*(N:ℝ)*(T+1-L:ℕ)/(L:ℝ) := by
  have hLr : (0:ℝ) < L := by exact_mod_cast hL
  have hc : ((largeCover L T N).card : ℝ) ≤
      ∑ j ∈ Icc L T, ((neighborCover (block j) N).card : ℝ) := by
    exact_mod_cast (card_biUnion_le (s := Icc L T) (t := fun j => neighborCover (block j) N))
  calc
    _ ≤ _ := hc
    _ ≤ ∑ j ∈ Icc L T, 2*(N:ℝ)*(4/(L:ℝ)) := by
      apply sum_le_sum
      intro j hj
      have hLj := (mem_Icc.mp hj).1
      have hm := (blockMass_le (hL.trans_le hLj)).trans
        (div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ 4) hLr (by exact_mod_cast hLj))
      exact (neighborCover_card (block j) N).trans
        (mul_le_mul_of_nonneg_left hm (by positivity))
    _ = _ := by simp [Nat.card_Icc]; ring

lemma mem_largeCover {n T L : ℕ} (hn : 0 < n) (hnT : n < 2^T)
    (hL : 2^L ≤ winner n) : n ∈ largeCover L T (2^T) := by
  have hp := winner_prime hn
  let j := Nat.log 2 (winner n)
  have hLj : L ≤ j := Nat.le_log_of_pow_le (by omega) hL
  have hjT : j ≤ T := by
    have hh := Nat.log_mono_right (b := 2) (winner_le hnT)
    simpa [Nat.log_pow (by omega : 1 < 2)] using hh
  apply mem_biUnion.mpr
  refine ⟨j,mem_Icc.mpr ⟨hLj,hjT⟩,mem_neighborCover hn hnT ?_⟩
  exact mem_block.mpr ⟨hp,Nat.pow_log_le_self 2 hp.ne_zero,
    Nat.lt_pow_succ_log_self (by omega) (winner n)⟩

def tailCount (K N : ℕ) : ℕ :=
  ((range N).filter fun n => K ≤ Erdos371SupercriticalPrimePairs.multiplicity n).card

/-- A finite dyadic tail bound, with no assumption about signed cancellation. -/
theorem tailCount_dyadic_bound {K H L : ℕ} (hK : 0 < K) (hH : 0 < H) (hL : 0 < L)
    (hLH : L*K ≤ H*(K-1)) (T : ℕ) :
    (tailCount K (2^T) : ℝ) ≤ (2:ℝ)^H + 8*(2:ℝ)^T*(T+1-L:ℕ)/(L:ℝ) := by
  have hs : (range (2^T)).filter (fun n => K ≤ Erdos371SupercriticalPrimePairs.multiplicity n) ⊆
      range (2^H) ∪ largeCover L T (2^T) := by
    intro n hn
    obtain ⟨hnT,hm⟩ := mem_filter.mp hn
    have hnT' := mem_range.mp hnT
    by_cases hsmall : n < 2^H
    · exact mem_union_left _ (mem_range.mpr hsmall)
    · have hHn : 2^H ≤ n+1 := by omega
      have htwo : 2 ≤ 2^H := by simpa using Nat.pow_le_pow_right (by omega : 0 < 2) hH
      have hn1 : 1 < n := by omega
      exact mem_union_right _ (mem_largeCover (by omega) hnT'
        (winner_lower_bound hn1 hK hm hHn hLH))
  have hc : tailCount K (2^T) ≤ 2^H + (largeCover L T (2^T)).card := by
    exact (card_le_card hs).trans (by simpa using card_union_le (range (2^H)) (largeCover L T (2^T)))
  have hcR : (tailCount K (2^T) : ℝ) ≤ (2:ℝ)^H + (largeCover L T (2^T)).card := by
    exact_mod_cast hc
  have hh := largeCover_card hL T (2^T)
  push_cast at hh
  linarith


lemma dyadic_parameters {K T : ℕ} (hK : 4 ≤ K) (hT : K^2 ≤ T) :
    let j := T/K
    0 < T-j ∧ 0 < T-2*j ∧
    (T-2*j)*K ≤ (T-j)*(K-1) ∧
    (T+1-(T-2*j))*K ≤ 6*(T-2*j) ∧ K ≤ j := by
  dsimp only
  let j := T/K
  have hK0 : 0 < K := by omega
  have hKj : K ≤ j := by
    apply (Nat.le_div_iff_mul_le hK0).mpr
    simpa [pow_two] using hT
  have hj : 0 < j := by omega
  have hprod : K*j ≤ T := by simpa [Nat.mul_comm] using Nat.div_mul_le_self T K
  have hrem : T < K*j+K := by
    have he := Nat.mod_add_div T K
    have hh := Nat.mod_lt T hK0
    dsimp [j]
    nlinarith
  have hfour : 4*j ≤ T := (Nat.mul_le_mul_right j hK).trans hprod
  have hH : (T-j)+j=T := Nat.sub_add_cancel (by omega)
  have hL : (T-2*j)+2*j=T := Nat.sub_add_cancel (by omega)
  have hKsub : K-1+1=K := by omega
  have hLhalf : K*j ≤ 2*(T-2*j) := by
    have hh := Nat.mul_le_mul_right j hK
    nlinarith
  change 0 < T-j ∧ 0 < T-2*j ∧ (T-2*j)*K ≤ (T-j)*(K-1) ∧
    (T+1-(T-2*j))*K ≤ 6*(T-2*j) ∧ K ≤ j
  refine ⟨by omega,by omega,?_,?_,hKj⟩
  · nlinarith
  · have hh : T+1-(T-2*j) ≤ 3*j := by omega
    have hmul := Nat.mul_le_mul_right K hh
    nlinarith

/-- The tail occupies at most `49/K` of a sufficiently large dyadic prefix. -/
theorem tailCount_dyadic_small {K T : ℕ} (hK : 4 ≤ K) (hT : K^2 ≤ T) :
    (tailCount K (2^T) : ℝ) ≤ 49*(2:ℝ)^T/(K:ℝ) := by
  obtain ⟨hH,hL,hLH,hwidth,hKj⟩ := dyadic_parameters hK hT
  have hK0 : 0 < K := by omega
  have hKr : (0:ℝ) < K := by exact_mod_cast hK0
  have hLr : (0:ℝ) < ((T-2*(T/K):ℕ):ℝ) := by exact_mod_cast hL
  have hb := tailCount_dyadic_bound hK0 hH hL hLH T
  have hwidthR : ((T+1-(T-2*(T/K)) : ℕ):ℝ)/(T-2*(T/K):ℕ) ≤ 6/(K:ℝ) := by
    apply (div_le_div_iff₀ hLr hKr).mpr
    exact_mod_cast hwidth
  have hsum : (T-T/K)+(T/K)=T := Nat.sub_add_cancel (Nat.div_le_self T K)
  have hpowK : (K:ℝ) ≤ (2:ℝ)^(T/K) := by
    exact_mod_cast hKj.trans (Nat.lt_two_pow_self.le)
  have hsmall : (2:ℝ)^(T-T/K) ≤ (2:ℝ)^T/(K:ℝ) := by
    apply (le_div_iff₀ hKr).mpr
    calc
      _ ≤ (2:ℝ)^(T-T/K)*(2:ℝ)^(T/K) := mul_le_mul_of_nonneg_left hpowK (by positivity)
      _ = _ := by rw [← pow_add,hsum]
  have hlarge : 8*(2:ℝ)^T*(T+1-(T-2*(T/K)):ℕ)/(T-2*(T/K):ℕ) ≤
      48*(2:ℝ)^T/(K:ℝ) := by
    calc
      _ = (8*(2:ℝ)^T)*(((T+1-(T-2*(T/K)):ℕ):ℝ)/(T-2*(T/K):ℕ)) := by ring
      _ ≤ (8*(2:ℝ)^T)*(6/(K:ℝ)) := mul_le_mul_of_nonneg_left hwidthR (by positivity)
      _ = _ := by ring
  calc
    _ ≤ _ := hb
    _ ≤ (2:ℝ)^T/(K:ℝ) + 48*(2:ℝ)^T/(K:ℝ) := add_le_add hsmall hlarge
    _ = _ := by ring

lemma tailCount_mono (K : ℕ) {M N : ℕ} (hMN : M ≤ N) :
    tailCount K M ≤ tailCount K N :=
  card_le_card (filter_subset_filter _ (range_mono hMN))

/-- An unsigned quantitative tail estimate in every sufficiently large prefix. -/
theorem tailCount_bound {K N : ℕ} (hK : 4 ≤ K) (hN : 2^(K^2) ≤ N) :
    (tailCount K N : ℝ)/(N:ℝ) ≤ 98/(K:ℝ) := by
  have hN0 : 0 < N := (Nat.pow_pos (by omega : 0 < 2)).trans_le hN
  have hNr : (0:ℝ) < N := by exact_mod_cast hN0
  have hKr : (0:ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  let T := Nat.log 2 N+1
  have hT : K^2 ≤ T := (Nat.le_log_of_pow_le (by omega) hN).trans (Nat.le_succ _)
  have hnT : N < 2^T := Nat.lt_pow_succ_log_self (by omega) N
  have hpow : 2^T ≤ 2*N := by
    have hh := Nat.pow_log_le_self 2 hN0.ne'
    dsimp [T]
    rw [pow_succ]
    nlinarith
  have hc : (tailCount K N : ℝ) ≤ tailCount K (2^T) := by
    exact_mod_cast tailCount_mono K hnT.le
  have hb := tailCount_dyadic_small hK hT
  have hpR : (2:ℝ)^T ≤ 2*(N:ℝ) := by exact_mod_cast hpow
  have hlarge : 49*(2:ℝ)^T/(K:ℝ) ≤ 98*(N:ℝ)/(K:ℝ) := by
    apply div_le_div_of_nonneg_right _ hKr.le
    nlinarith
  apply (div_le_iff₀ hNr).mpr
  have hh := hc.trans (hb.trans hlarge)
  simpa only [div_mul_eq_mul_div] using hh

/-- Unbounded multiplicity nevertheless has a tight distribution. This does
not assert uniform integrability or cancellation of any signed average. -/
theorem multiplicity_tail_tight (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℕ, 4 ≤ K ∧ ∀ᶠ N in atTop,
      (tailCount K N : ℝ)/(N:ℝ) < ε := by
  obtain ⟨K,hK⟩ := exists_nat_gt (98/ε+4)
  have hK4 : 4 ≤ K := by
    have : (4:ℝ) < K := by have := div_pos (by norm_num : (0:ℝ) < 98) hε; linarith
    exact_mod_cast this.le
  have hKr : (0:ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  have hsmall : 98/(K:ℝ) < ε := by
    apply (div_lt_iff₀ hKr).mpr
    have hh : 98/ε < (K:ℝ) := by linarith
    have hh' := (div_lt_iff₀ hε).mp hh
    linarith
  refine ⟨K,hK4,?_⟩
  filter_upwards [eventually_ge_atTop (2^(K^2))] with N hN
  exact (tailCount_bound hK4 hN).trans_lt hsmall

end Erdos371SupercriticalMultiplicityTail

#print axioms Erdos371SupercriticalMultiplicityTail.multiplicity_power_bound
#print axioms Erdos371SupercriticalMultiplicityTail.tailCount_dyadic_bound
#print axioms Erdos371SupercriticalMultiplicityTail.tailCount_bound
#print axioms Erdos371SupercriticalMultiplicityTail.multiplicity_tail_tight
