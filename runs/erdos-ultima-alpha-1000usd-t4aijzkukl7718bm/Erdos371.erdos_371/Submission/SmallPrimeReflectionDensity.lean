import Submission.SmallPrimeReflection

/-! The least-losing-prime reflection compresses almost all of a counting
interval into an arbitrarily short initial subinterval. This is not a
measure-preserving pairing. -/
namespace Erdos371
open Finset Filter
open scoped Topology

lemma adjacent_preimage_card_le (s T : Finset ℕ) :
    (s.filter fun n => n ∈ T ∨ n+1 ∈ T).card ≤ 2*T.card := by
  have hsub : (s.filter fun n => n ∈ T ∨ n+1 ∈ T) ⊆
      T ∪ T.image (fun m => m-1) := by
    intro n hn
    rcases (mem_filter.mp hn).2 with h | h
    · exact mem_union_left _ h
    · exact mem_union_right _ (mem_image.mpr ⟨n+1,h,by omega⟩)
  have h := (card_le_card hsub).trans (card_union_le _ _)
  have h' := card_image_le (s := T) (f := fun m => m-1)
  omega

lemma large_maxPrimeFac_count_le (K N : ℕ) :
    ((range (N+1)).filter fun n => 1 < n ∧ N < K*Nat.maxPrimeFac n).card ≤
      K*((N+1).primesBelow).card := by
  have hs : ((range (N+1)).filter fun n => 1 < n ∧ N < K*Nat.maxPrimeFac n) ⊆
      (((N+1).primesBelow) ×ˢ range K).image (fun z : ℕ × ℕ => z.1*z.2) := by
    intro n hn
    obtain ⟨hnN,hn,hK⟩ := mem_filter.mp hn
    have hnN' := mem_range.mp hnN
    have hp := Nat.prime_maxPrimeFac_of_one_lt n hn
    have hpN : Nat.maxPrimeFac n < N+1 := Nat.maxPrimeFac_le.trans_lt hnN'
    have hc : primeCofactor n < K := by
      change n/Nat.maxPrimeFac n < K
      apply (Nat.div_lt_iff_lt_mul hp.pos).mpr
      omega
    exact mem_image.mpr ⟨(Nat.maxPrimeFac n,primeCofactor n),
      mem_product.mpr ⟨Nat.mem_primesBelow.mpr ⟨hpN,hp⟩,mem_range.mpr hc⟩,
      maxPrimeFac_mul_primeCofactor n⟩
  exact (card_le_card hs).trans (by
    simpa only [card_product,card_range,Nat.mul_comm] using
      card_image_le (s := ((N+1).primesBelow) ×ˢ range K)
        (f := fun z : ℕ × ℕ => z.1*z.2))

lemma large_primeWinner_count_le (K N : ℕ) :
    ((range N).filter fun n => 1 < n ∧ N < K*primeWinner n).card ≤
      2*K*((N+1).primesBelow).card := by
  let T := (range (N+1)).filter fun n => 1 < n ∧ N < K*Nat.maxPrimeFac n
  have hs : ((range N).filter fun n => 1 < n ∧ N < K*primeWinner n) ⊆
      (range N).filter (fun n => n ∈ T ∨ n+1 ∈ T) := by
    intro n hn
    obtain ⟨hnN,hn,hK⟩ := mem_filter.mp hn
    have hnN' := mem_range.mp hnN
    apply mem_filter.mpr ⟨hnN,?_⟩
    by_cases h : Nat.maxPrimeFac n ≤ Nat.maxPrimeFac (n+1)
    · apply Or.inr
      exact mem_filter.mpr ⟨mem_range.mpr (by omega),by omega,by
        simpa only [primeWinner,max_eq_right h] using hK⟩
    · apply Or.inl
      exact mem_filter.mpr ⟨mem_range.mpr (by omega),hn,by
        simpa only [primeWinner,max_eq_left (not_le.mp h).le] using hK⟩
  calc
    _ ≤ 2*T.card := (card_le_card hs).trans (adjacent_preimage_card_le _ T)
    _ ≤ _ := by
      have := Nat.mul_le_mul_left 2 (large_maxPrimeFac_count_le K N)
      simpa only [Nat.mul_assoc] using this

lemma primesBelow_card_div_tendsto_zero :
    Tendsto (fun N : ℕ => (((N+1).primesBelow).card : ℝ)/N) atTop (nhds 0) := by
  apply squeeze_zero (fun _ => by positivity) _ primeWinnerLabels_card_tendsto_zero
  intro N
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
  exact_mod_cast card_le_card (subset_insert 1 ((N+1).primesBelow))

theorem large_primeWinner_count_tendsto_zero (K : ℕ) :
    Tendsto (fun N =>
      (((range N).filter fun n => 1 < n ∧ N < K*primeWinner n).card : ℝ)/N)
      atTop (nhds 0) := by
  have ht := primesBelow_card_div_tendsto_zero.const_mul (2*K : ℝ)
  simp only [mul_zero] at ht
  apply squeeze_zero (fun _ => by positivity) _ ht
  intro N
  rw [← mul_div_assoc]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
  exact_mod_cast large_primeWinner_count_le K N

lemma large_leastLosingPrime_count_le (A N : ℕ) :
    ((range N).filter fun n => 1 < n ∧ A < leastLosingPrime n).card ≤
      2*roughNumberCount A (N+1) := by
  let T := (range (N+1)).filter fun n => 1 < n ∧ A < n.minFac
  have hs : ((range N).filter fun n => 1 < n ∧ A < leastLosingPrime n) ⊆
      (range N).filter (fun n => n ∈ T ∨ n+1 ∈ T) := by
    intro n hn
    obtain ⟨hnN,hn,hA⟩ := mem_filter.mp hn
    have hnN' := mem_range.mp hnN
    apply mem_filter.mpr ⟨hnN,?_⟩
    by_cases h : Nat.maxPrimeFac n < Nat.maxPrimeFac (n+1)
    · exact Or.inl (mem_filter.mpr ⟨mem_range.mpr (by omega),hn,by
        simpa only [leastLosingPrime,losingNumber,if_pos h] using hA⟩)
    · exact Or.inr (mem_filter.mpr ⟨mem_range.mpr (by omega),by omega,by
        simpa only [leastLosingPrime,losingNumber,if_neg h] using hA⟩)
  exact (card_le_card hs).trans (adjacent_preimage_card_le _ T)

lemma smallPrimeReflection_large_image_count_le (ε : ℝ) (hε : 0 < ε)
    (A K N : ℕ) (hK : (A : ℝ) < K*ε) :
    ((range N).filter fun n => ε*N ≤ (smallPrimeReflection n : ℝ)).card ≤
      2+2*roughNumberCount A (N+1)+2*K*((N+1).primesBelow).card := by
  let E := (range N).filter fun n => 1 < n ∧ A < leastLosingPrime n
  let H := (range N).filter fun n => 1 < n ∧ N < K*primeWinner n
  have hs : ((range N).filter fun n => ε*N ≤ (smallPrimeReflection n : ℝ)) ⊆
      range 2 ∪ E ∪ H := by
    intro n hn
    obtain ⟨hnN,he⟩ := mem_filter.mp hn
    by_cases hn1 : 1 < n
    · by_cases hA : A < leastLosingPrime n
      · exact mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨hnN,hn1,hA⟩))
      · refine mem_union_right _ (mem_filter.mpr ⟨hnN,hn1,?_⟩)
        by_contra hN
        have hr := (smallPrimeReflection_bounds n hn1).2
        have hbound : smallPrimeReflection n < A*primeWinner n :=
          hr.trans_le (Nat.mul_le_mul_right _ (not_lt.mp hA))
        have hbound' : (smallPrimeReflection n : ℝ) < A*primeWinner n := by exact_mod_cast hbound
        have hN' : (K : ℝ)*primeWinner n ≤ N := by exact_mod_cast not_lt.mp hN
        have hp : (0 : ℝ) ≤ primeWinner n := Nat.cast_nonneg _
        nlinarith
    · exact mem_union_left _ (mem_union_left _ (mem_range.mpr (by omega)))
  have hc := (card_le_card hs).trans (card_union_le _ _)
  have hc' := card_union_le (range 2) E
  have he := large_leastLosingPrime_count_le A N
  have hh := large_primeWinner_count_le K N
  change E.card ≤ _ at he
  change H.card ≤ _ at hh
  simp only [card_range] at hc'
  omega

lemma roughNumberCount_le_coprimeCount (M N : ℕ) (hM : 0 < M) :
    roughNumberCount M N ≤ ((range N).filter fun n => M.Coprime n).card := by
  apply card_le_card
  intro n hn
  obtain ⟨hnN,_,hmin⟩ := mem_filter.mp hn
  exact mem_filter.mpr ⟨hnN,(Nat.coprime_of_lt_minFac hM.ne' hmin).symm⟩

/-- Almost all inputs are reflected to less than ε times the endpoint,
for every positive fixed ε. This does not assert small multiplicities. -/
theorem smallPrimeReflection_large_image_tendsto_zero (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun N : ℕ =>
      (((range N).filter fun n => ε*N ≤ (smallPrimeReflection n : ℝ)).card : ℝ)/N)
      atTop (nhds 0) := by
  apply tendsto_order.mpr
  constructor
  · intro δ hδ
    exact Eventually.of_forall fun N => hδ.trans_le (by positivity)
  · intro δ hδ
    obtain ⟨M,hM,hr⟩ := exists_small_totient_ratio (δ/4) (by positivity)
    obtain ⟨K,hK⟩ := exists_nat_gt ((M : ℝ)/ε)
    have hK' : (M : ℝ) < K*ε := (div_lt_iff₀ hε).mp hK
    have ht := (density_iff_count (fun n => M.Coprime n) _).mp
      (periodic_predicate_hasDensity (fun n => M.Coprime n) M hM (Nat.periodic_coprime M))
    have ht' := ((ht.const_mul 2).add
      (primesBelow_card_div_tendsto_zero.const_mul (2*K : ℝ))).add
        (tendsto_one_div_atTop_nhds_zero_nat.const_mul 4)
    have hlim : 2*((((range M).filter fun n => M.Coprime n).card : ℝ)/M)+0+0 < δ := by
      rw [← Nat.totient_eq_card_coprime]
      linarith
    simp only [mul_zero] at ht'
    filter_upwards [ht'.eventually_lt_const hlim] with N hN
    have hc := smallPrimeReflection_large_image_count_le ε hε M K N hK'
    have hrN := (roughNumberCount_succ_le M N).trans
      (Nat.add_le_add_right (roughNumberCount_le_coprimeCount M N hM) 1)
    have hb : ((range N).filter fun n => ε*N ≤ (smallPrimeReflection n : ℝ)).card ≤
        2*((range N).filter fun n => M.Coprime n).card+
          2*K*((N+1).primesBelow).card+4 := by omega
    have hd := div_le_div_of_nonneg_right ((Nat.cast_le (α := ℝ)).mpr hb)
      (Nat.cast_nonneg (α := ℝ) N)
    push_cast at hd
    simp only [add_div,mul_div_assoc] at hd
    exact hd.trans_lt (by simpa only [mul_one_div] using hN)

#print axioms large_primeWinner_count_tendsto_zero
#print axioms smallPrimeReflection_large_image_tendsto_zero
end Erdos371
