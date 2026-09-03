import Submission.SmallPrimeReflectionDensity

/-! Unconditional cancellation of cross-prime skew on products at most the
sample size. The number of such unordered prime pairs is o(N). -/
namespace Erdos371
open Finset Filter
open scoped Topology

def shortPrimePairs (N : ℕ) : Finset (ℕ×ℕ) :=
  ((N+1).primesBelow ×ˢ (N+1).primesBelow).filter fun pq => pq.1 < pq.2 ∧ pq.1*pq.2 ≤ N

lemma ordered_prime_product_injective (p q r s : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hr : r.Prime) (hs : s.Prime) (hpq : p < q) (hrs : r < s) (he : p*q=r*s) :
    p=r ∧ q=s := by
  have hmin := congrArg Nat.minFac he
  rw [minFac_mul_of_one_lt p q hp.one_lt hq.one_lt,
    minFac_mul_of_one_lt r s hr.one_lt hs.one_lt,
    hp.minFac_eq,hq.minFac_eq,hr.minFac_eq,hs.minFac_eq,
    min_eq_left hpq.le,min_eq_left hrs.le] at hmin
  refine ⟨hmin,?_⟩
  rw [← hmin] at he
  exact (Nat.mul_left_cancel_iff hp.pos).mp he

lemma shortPrimePairs_count_bound (B N : ℕ) :
    (shortPrimePairs N).card ≤ (B+1)*(N+1).primesBelow.card+roughNumberCount B (N+1) := by
  have hlo : ((shortPrimePairs N).filter (fun pq => pq.1 ≤ B)).card ≤
      (B+1)*(N+1).primesBelow.card := by
    have hsub : (shortPrimePairs N).filter (fun pq => pq.1 ≤ B) ⊆
        range (B+1) ×ˢ (N+1).primesBelow := by
      intro pq hpq
      obtain ⟨hm,hB⟩ := mem_filter.mp hpq
      have hq := (mem_product.mp (mem_filter.mp hm).1).2
      exact mem_product.mpr ⟨mem_range.mpr (by omega),hq⟩
    simpa only [card_product,card_range] using card_le_card hsub
  have hhi : ((shortPrimePairs N).filter (fun pq => ¬pq.1 ≤ B)).card ≤
      roughNumberCount B (N+1) := by
    unfold roughNumberCount
    apply card_le_card_of_injOn (fun pq : ℕ×ℕ => pq.1*pq.2)
    · intro pq hpq
      obtain ⟨hm,hB⟩ := mem_filter.mp hpq
      obtain ⟨hm,hpq,hN⟩ := mem_filter.mp hm
      obtain ⟨hp,hq⟩ := mem_product.mp hm
      have hpp := (Nat.mem_primesBelow.mp hp).2
      have hqp := (Nat.mem_primesBelow.mp hq).2
      have h1 := hpp.two_le
      have h2 := hqp.two_le
      simp only [mem_coe,mem_filter,mem_range]
      refine ⟨by omega,by nlinarith,?_⟩
      rw [minFac_mul_of_one_lt _ _ hpp.one_lt hqp.one_lt,hpp.minFac_eq,hqp.minFac_eq,
        min_eq_left hpq.le]
      omega
    · intro a ha b hb he
      have ha' := mem_filter.mp (mem_filter.mp ha).1
      have hb' := mem_filter.mp (mem_filter.mp hb).1
      obtain ⟨hp,hq⟩ := mem_product.mp ha'.1
      obtain ⟨hr,hs⟩ := mem_product.mp hb'.1
      obtain ⟨h1,h2⟩ := ordered_prime_product_injective _ _ _ _
        (Nat.mem_primesBelow.mp hp).2 (Nat.mem_primesBelow.mp hq).2
        (Nat.mem_primesBelow.mp hr).2 (Nat.mem_primesBelow.mp hs).2 ha'.2.1 hb'.2.1 he
      exact Prod.ext h1 h2
  have he := card_filter_add_card_filter_not (s := shortPrimePairs N) (fun pq => pq.1 ≤ B)
  omega

/-- This is elementary density-zero counting, not a prime number theorem. -/
theorem shortPrimePairs_count_zero :
    Tendsto (fun N : ℕ => ((shortPrimePairs N).card : ℝ)/N) atTop (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro ε hε
    exact Eventually.of_forall (fun N => hε.trans_le (by positivity))
  · intro ε hε
    obtain ⟨M,hM,hr⟩ := exists_small_totient_ratio ε hε
    have hcp := (density_iff_count (fun n => M.Coprime n) _).mp
      (periodic_predicate_hasDensity (fun n => M.Coprime n) M hM (Nat.periodic_coprime M))
    have hcp' : Tendsto (fun N : ℕ => (((range N).filter fun n => M.Coprime n).card : ℝ)/N)
        atTop (𝓝 ((M.totient : ℝ)/M)) := by
      simpa only [← Nat.totient_eq_card_coprime] using hcp
    have ht := ((primesBelow_card_div_tendsto_zero.const_mul (M+1 : ℝ)).add hcp').add
      tendsto_one_div_atTop_nhds_zero_nat
    simp only [mul_zero,zero_add,add_zero] at ht
    filter_upwards [ht.eventually_lt_const hr] with N hN
    have hR : roughNumberCount M (N+1) ≤ ((range N).filter fun n => M.Coprime n).card+1 := by
      apply (roughNumberCount_succ_le M N).trans
      apply Nat.add_le_add_right
      apply card_le_card
      intro n hn
      obtain ⟨hnN,_,hmin⟩ := mem_filter.mp hn
      exact mem_filter.mpr ⟨hnN,(Nat.coprime_of_lt_minFac hM.ne' hmin).symm⟩
    have hb := (shortPrimePairs_count_bound M N).trans (Nat.add_le_add_left hR _)
    have hbR : ((shortPrimePairs N).card : ℝ) ≤
        (M+1 : ℝ)*(N+1).primesBelow.card+((range N).filter fun n => M.Coprime n).card+1 := by
      exact_mod_cast hb
    have hh := div_le_div_of_nonneg_right hbR (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
    apply hh.trans_lt
    convert hN using 1; ring

noncomputable def shortPrimePairSkew (N n : ℕ) : ℝ :=
  ∑ pq ∈ shortPrimePairs N, pairIndicatorDifference pq.1 pq.2 n

lemma shortPrimePairSkew_prefix_bound (N M : ℕ) :
    |∑ n ∈ range M, shortPrimePairSkew N (n+1)| ≤ (shortPrimePairs N).card := by
  unfold shortPrimePairSkew
  rw [sum_comm]
  calc
    _ ≤ ∑ pq ∈ shortPrimePairs N, |∑ n ∈ range M, pairIndicatorDifference pq.1 pq.2 (n+1)| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ _pq ∈ shortPrimePairs N, (1 : ℝ) := by
      apply sum_le_sum
      intro pq hpq
      obtain ⟨hm,_⟩ := mem_filter.mp hpq
      obtain ⟨hp,hq⟩ := mem_product.mp hm
      rw [← bilinearCount_difference_eq_sum,← Real.norm_eq_abs]
      exact bilinearCount_discrepancy_le_one M pq.1 pq.2
        (Nat.mem_primesBelow.mp hp).2.pos (Nat.mem_primesBelow.mp hq).2.pos
    _ = _ := by simp

/-- Every pair retains its orientation; the total signed error is o(N). -/
theorem shortPrimePairSkew_mean_zero :
    Tendsto (fun N : ℕ => (∑ n ∈ range N, shortPrimePairSkew N (n+1))/N) atTop (𝓝 0) := by
  apply squeeze_zero_norm _ shortPrimePairs_count_zero
  intro N
  rw [norm_div,Real.norm_natCast,Real.norm_eq_abs]
  exact div_le_div_of_nonneg_right (shortPrimePairSkew_prefix_bound N N) (Nat.cast_nonneg N)

lemma shortPrimePairs_succ_count_zero :
    Tendsto (fun N : ℕ => ((shortPrimePairs (N+1)).card : ℝ)/N) atTop (𝓝 0) := by
  have ht := shortPrimePairs_count_zero.comp (tendsto_add_atTop_nat 1)
  have hr : Tendsto (fun N : ℕ => ((N : ℝ)+1)/N) atTop (𝓝 1) := by
    have hh := tendsto_one_div_atTop_nhds_zero_nat.const_add (1 : ℝ)
    simp only [add_zero] at hh
    apply hh.congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
    have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    field_simp
  have hh := ht.mul hr
  simp only [zero_mul,Function.comp_def] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
  simp only [Nat.cast_add,Nat.cast_one]
  have hn : (N : ℝ)+1 ≠ 0 := by positivity
  field_simp

lemma shortPrimePairSkew_succ_mean_zero :
    Tendsto (fun N : ℕ => (∑ n ∈ range N, shortPrimePairSkew (N+1) (n+1))/N) atTop (𝓝 0) := by
  apply squeeze_zero_norm _ shortPrimePairs_succ_count_zero
  intro N
  rw [norm_div,Real.norm_natCast,Real.norm_eq_abs]
  exact div_le_div_of_nonneg_right (shortPrimePairSkew_prefix_bound (N+1) N) (Nat.cast_nonneg N)

#print axioms shortPrimePairs_count_zero
#print axioms shortPrimePairSkew_mean_zero
end Erdos371
