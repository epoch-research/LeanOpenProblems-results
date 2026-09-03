import FormalConjecturesUtil
import Submission.MonotoneAdditiveReversal

/-! A uniform half-descent upper bound for a nonnegative logarithmic term
plus arbitrary additive weights on a FIXED finite prime support. The error
is independent of all coefficients. This does not cover the growing prime
support in `height N` and does not prove Erdős 371. -/

namespace Erdos371FiniteSupportAdditiveDescent

open Finset Filter
open scoped Topology
attribute [local instance] Classical.propDecidable

noncomputable def descentCount (f : ℕ → ℝ) (N : ℕ) : ℕ :=
  ((range N).filter (fun n => f (n+1)<f n)).card

lemma reflected_period_half {Q : ℕ} (g : ℕ → ℝ)
    (href : ∀ n, n ≤ Q → g (Q-n)=g n) :
    2*descentCount g Q ≤ Q := by
  have hc : descentCount g Q ≤
      ((range Q).filter (fun n => ¬g (n+1)<g n)).card := by
    apply card_le_card_of_injOn (fun n => Q-1-n)
    · intro n hn
      change n ∈ (range Q).filter (fun n => g (n+1)<g n) at hn
      obtain ⟨hn,hd⟩ := mem_filter.mp hn
      have hnQ := mem_range.mp hn
      change Q-1-n ∈ (range Q).filter (fun n => ¬g (n+1)<g n)
      have he₁ : Q-1-n+1=Q-n := by omega
      have he₂ : Q-1-n=Q-(n+1) := by omega
      refine mem_filter.mpr ⟨mem_range.mpr (by omega),?_⟩
      rw [he₁,href n (by omega),he₂,href (n+1) (by omega)]
      exact not_lt_of_ge hd.le
    · intro n hn m hm he
      have hnQ := mem_range.mp (mem_filter.mp hn).1
      have hmQ := mem_range.mp (mem_filter.mp hm).1
      change Q-1-n=Q-1-m at he
      omega
  have hs := card_filter_add_card_filter_not (s := range Q) (fun n => g (n+1)<g n)
  change descentCount g Q+_ = _ at hs
  rw [card_range] at hs
  omega

lemma reflected_period_prefix_bound {Q : ℕ} (hQ : 0<Q) (g : ℕ → ℝ)
    (hper : ∀ n, g (n+Q)=g n)
    (href : ∀ n, n ≤ Q → g (Q-n)=g n) (N : ℕ) :
    2*descentCount g N ≤ N+2*Q := by
  have hp (n : ℕ) : (g (n+Q+1)<g (n+Q)) ↔ g (n+1)<g n := by
    rw [show n+Q+1=(n+1)+Q by omega,hper,hper]
  have hh := Erdos371Exploration.periodic_count_remainder
    (fun n => g (n+1)<g n) hp N
  change descentCount g N=N/Q*descentCount g Q+descentCount g (N%Q) at hh
  have hr : descentCount g (N%Q) ≤ Q :=
    (card_filter_le _ _).trans (by simpa using (Nat.mod_lt N hQ).le)
  have hmain := Nat.mul_le_mul_left (N/Q) (reflected_period_half g href)
  calc
    2*descentCount g N = N/Q*(2*descentCount g Q)+2*descentCount g (N%Q) := by
      rw [hh]; ring
    _ ≤ N/Q*Q+2*Q := Nat.add_le_add hmain (Nat.mul_le_mul_left 2 hr)
    _ ≤ N+2*Q := Nat.add_le_add_right (Nat.div_mul_le_self N Q) _

/-- Count divisibility by the first `k` powers, with a periodic convention at zero. -/
def truncatedVal (p k n : ℕ) : ℕ := ((Icc 1 k).filter (fun j => p^j ∣ n)).card

lemma truncatedVal_eq {p k n : ℕ} (hp : p.Prime) (hn : n ≠ 0)
    (hbad : ¬p^k ∣ n) : truncatedVal p k n=n.factorization p := by
  have hv : n.factorization p<k := by
    rw [hp.pow_dvd_iff_le_factorization hn] at hbad
    omega
  have he : (Icc 1 k).filter (fun j => p^j ∣ n) = Icc 1 (n.factorization p) := by
    ext j
    simp only [mem_filter,mem_Icc,hp.pow_dvd_iff_le_factorization hn]
    omega
  simp [truncatedVal,he]

noncomputable def period (s : Finset ℕ) (k : ℕ) : ℕ := ∏ p ∈ s, p^k

lemma period_pos {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime) (k : ℕ) : 0<period s k :=
  prod_pos fun p hp => pow_pos (hs p hp).pos _

lemma power_dvd_period {s : Finset ℕ} {p k j : ℕ} (hp : p ∈ s) (hj : j ≤ k) :
    p^j ∣ period s k :=
  (pow_dvd_pow p hj).trans (dvd_prod_of_mem (fun p => p^k) hp)

noncomputable def truncated (s : Finset ℕ) (k : ℕ) (w : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ p ∈ s, w p*truncatedVal p k n

lemma truncated_periodic (s : Finset ℕ) (k : ℕ) (w : ℕ → ℝ) (n : ℕ) :
    truncated s k w (n+period s k)=truncated s k w n := by
  apply sum_congr rfl
  intro p hp
  congr 2
  unfold truncatedVal
  congr 1
  apply filter_congr
  intro j hj
  exact (Nat.dvd_add_iff_left (power_dvd_period hp (mem_Icc.mp hj).2)).symm

lemma truncated_reflection (s : Finset ℕ) (k : ℕ) (w : ℕ → ℝ)
    (n : ℕ) (hn : n ≤ period s k) :
    truncated s k w (period s k-n)=truncated s k w n := by
  apply sum_congr rfl
  intro p hp
  congr 2
  unfold truncatedVal
  congr 1
  apply filter_congr
  intro j hj
  exact Nat.dvd_sub_iff_right hn (power_dvd_period hp (mem_Icc.mp hj).2)

noncomputable def additive (s : Finset ℕ) (w : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ p ∈ s, w p*n.factorization p

noncomputable def height (s : Finset ℕ) (a : ℝ) (w : ℕ → ℝ) (n : ℕ) : ℝ :=
  a*Real.log n+additive s w n

noncomputable def bad (s : Finset ℕ) (k N : ℕ) : Finset ℕ :=
  (range N).filter (fun n => n=0 ∨ ∃ p ∈ s, p^k ∣ n ∨ p^k ∣ n+1)

lemma height_descent_subset {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime)
    {a : ℝ} (ha : 0 ≤ a) (w : ℕ → ℝ) (k N : ℕ) :
    (range N).filter (fun n => height s a w (n+1)<height s a w n) ⊆
      (range N).filter (fun n => truncated s k w (n+1)<truncated s k w n) ∪ bad s k N := by
  intro n hn
  obtain ⟨hnN,hd⟩ := mem_filter.mp hn
  by_cases hb : n=0 ∨ ∃ p ∈ s, p^k ∣ n ∨ p^k ∣ n+1
  · exact mem_union_right _ (mem_filter.mpr ⟨hnN,hb⟩)
  · have hn0 : n ≠ 0 := fun he => hb (Or.inl he)
    have hval (p : ℕ) (hp : p ∈ s) :
        truncatedVal p k n=n.factorization p ∧
        truncatedVal p k (n+1)=(n+1).factorization p := by
      have h₁ : ¬p^k ∣ n := fun h => hb (Or.inr ⟨p,hp,Or.inl h⟩)
      have h₂ : ¬p^k ∣ n+1 := fun h => hb (Or.inr ⟨p,hp,Or.inr h⟩)
      exact ⟨truncatedVal_eq (hs p hp) hn0 h₁,
        truncatedVal_eq (hs p hp) (by omega) h₂⟩
    have he₁ : truncated s k w n=additive s w n :=
      sum_congr rfl fun p hp => by rw [(hval p hp).1]
    have he₂ : truncated s k w (n+1)=additive s w (n+1) :=
      sum_congr rfl fun p hp => by rw [(hval p hp).2]
    refine mem_union_left _ (mem_filter.mpr ⟨hnN,?_⟩)
    rw [he₁,he₂]
    have hl : Real.log (n : ℝ) ≤ Real.log (n+1 : ℕ) :=
      Real.log_le_log (Nat.cast_pos.mpr (by omega)) (by exact_mod_cast Nat.le_succ n)
    have hm := mul_le_mul_of_nonneg_left hl ha
    unfold height at hd
    linarith

lemma multiples_count_le (m N : ℕ) :
    ((range N).filter (fun n => m ∣ n)).card ≤ N/m+1 := by
  have hsub : (range N).filter (fun n => m ∣ n) ⊆
      insert 0 ((range (N+1)).filter (fun n => n ≠ 0 ∧ m ∣ n)) := by
    intro n hn
    obtain ⟨hnN,hd⟩ := mem_filter.mp hn
    by_cases hn0 : n=0
    · simp [hn0]
    · exact mem_insert_of_mem (mem_filter.mpr
        ⟨mem_range.mpr (by have := mem_range.mp hnN; omega),hn0,hd⟩)
  have hc := (card_le_card hsub).trans (card_insert_le _ _)
  simpa only [Nat.card_multiples'] using hc

lemma either_multiple_count_le (m N : ℕ) :
    ((range N).filter (fun n => m ∣ n ∨ m ∣ n+1)).card ≤ 2*(N/m)+1 := by
  rw [filter_or]
  have hh := card_union_le ((range N).filter (fun n => m ∣ n))
    ((range N).filter (fun n => m ∣ n+1))
  rw [Nat.card_multiples] at hh
  have hm := multiples_count_le m N
  exact hh.trans (by omega)

lemma bad_card_bound (s : Finset ℕ) (k N : ℕ) :
    (bad s k N).card ≤ 1+∑ p ∈ s, (2*(N/(p^k))+1) := by
  have hsub : bad s k N ⊆ {0} ∪
      s.biUnion (fun p => (range N).filter (fun n => p^k ∣ n ∨ p^k ∣ n+1)) := by
    intro n hn
    obtain ⟨hnN,hb⟩ := mem_filter.mp hn
    rcases hb with rfl | ⟨p,hp,hd⟩
    · exact mem_union_left _ (mem_singleton_self _)
    · exact mem_union_right _ (mem_biUnion.mpr ⟨p,hp,mem_filter.mpr ⟨hnN,hd⟩⟩)
  calc
    _ ≤ _ := card_le_card hsub
    _ ≤ 1+(s.biUnion (fun p => (range N).filter
        (fun n => p^k ∣ n ∨ p^k ∣ n+1))).card := by simpa using card_union_le {0} _
    _ ≤ 1+∑ p ∈ s, ((range N).filter (fun n => p^k ∣ n ∨ p^k ∣ n+1)).card :=
      Nat.add_le_add_left card_biUnion_le 1
    _ ≤ _ := Nat.add_le_add_left (sum_le_sum fun p _ => either_multiple_count_le (p^k) N) 1

lemma bad_card_real_bound (s : Finset ℕ) (k N : ℕ) :
    ((bad s k N).card : ℝ) ≤ 1+2*(N : ℝ)*(∑ p ∈ s, (1 : ℝ)/(p^k : ℕ))+s.card := by
  have hb := Nat.cast_le (α := ℝ).mpr (bad_card_bound s k N)
  push_cast at hb
  apply hb.trans
  calc
    1+∑ p ∈ s, (2*((N/p^k : ℕ) : ℝ)+1) ≤
        1+∑ p ∈ s, (2*((N : ℝ)/(p^k : ℕ))+1) := by
      apply add_le_add le_rfl
      exact sum_le_sum fun p _ => add_le_add
        (mul_le_mul_of_nonneg_left Nat.cast_div_le (by norm_num)) le_rfl
    _ = _ := by
      have he (p : ℕ) : 2*((N : ℝ)/(p^k : ℕ))=2*(N : ℝ)*((1 : ℝ)/(p^k : ℕ)) := by ring
      simp only [he,sum_add_distrib,← mul_sum,sum_const,nsmul_eq_mul,mul_one]
      ring

lemma descent_count_real_bound {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime)
    {a : ℝ} (ha : 0 ≤ a) (w : ℕ → ℝ) (k N : ℕ) :
    (descentCount (height s a w) N : ℝ) ≤ (N : ℝ)/2+period s k+1+
      2*(N : ℝ)*(∑ p ∈ s, (1 : ℝ)/(p^k : ℕ))+s.card := by
  have hc := (card_le_card (height_descent_subset hs ha w k N)).trans (card_union_le _ _)
  change descentCount (height s a w) N ≤ descentCount (truncated s k w) N+(bad s k N).card at hc
  have hc' := Nat.cast_le (α := ℝ).mpr hc
  have ht := reflected_period_prefix_bound (period_pos hs k) (truncated s k w)
    (truncated_periodic s k w) (truncated_reflection s k w) N
  have ht' := Nat.cast_le (α := ℝ).mpr ht
  push_cast at hc' ht'
  have hb := bad_card_real_bound s k N
  linarith

lemma descent_ratio_bound {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime)
    {a : ℝ} (ha : 0 ≤ a) (w : ℕ → ℝ) (k : ℕ) {N : ℕ} (hN : 0<N) :
    (descentCount (height s a w) N : ℝ)/N ≤ 1/2+
      ((period s k : ℝ)+1+s.card)/N+2*(∑ p ∈ s, (1 : ℝ)/(p^k : ℕ)) := by
  apply (div_le_div_of_nonneg_right (descent_count_real_bound hs ha w k N)
    (Nat.cast_nonneg (α := ℝ) N)).trans_eq
  have hn : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  field_simp
  ring

lemma reciprocal_tail_tendsto {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime) :
    Tendsto (fun k : ℕ => ∑ p ∈ s, (1 : ℝ)/(p^k : ℕ)) atTop (𝓝 (0 : ℝ)) := by
  have h (p : ℕ) (hp : p ∈ s) :
      Tendsto (fun k : ℕ => (1 : ℝ)/(p^k : ℕ)) atTop (𝓝 (0 : ℝ)) := by
    have hp1 : (1 : ℝ)<p := Nat.one_lt_cast.mpr (hs p hp).one_lt
    simpa only [Nat.cast_pow,one_div] using
      (tendsto_inv_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt hp1))
  simpa using tendsto_finset_sum s h

/-- The cutoff is uniform in the logarithmic coefficient and in every prime
weight, but the finite support must be fixed before choosing the cutoff. -/
theorem uniform_finite_support_bound {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime)
    (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ N : ℕ in atTop, ∀ (a : ℝ) (w : ℕ → ℝ), 0 ≤ a →
      (descentCount (height s a w) N : ℝ)/N ≤ 1/2+ε := by
  obtain ⟨k,hk⟩ := ((reciprocal_tail_tendsto hs).eventually
    (gt_mem_nhds (show (0 : ℝ)<ε/4 by positivity))).exists
  have he := (tendsto_const_div_atTop_nhds_zero_nat
    ((period s k : ℝ)+1+s.card)).eventually (gt_mem_nhds (half_pos hε))
  filter_upwards [he,eventually_gt_atTop 0] with N hsmall hN
  intro a w ha
  have hb := descent_ratio_bound hs ha w k hN
  linarith

lemma height_completely_additive (s : Finset ℕ) (a : ℝ) (w : ℕ → ℝ)
    {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    height s a w (m*n)=height s a w m+height s a w n := by
  simp only [height,additive,Nat.cast_mul,Real.log_mul
    (Nat.cast_ne_zero.mpr hm) (Nat.cast_ne_zero.mpr hn),Nat.factorization_mul hm hn,
    Finsupp.add_apply,Nat.cast_add,mul_add,sum_add_distrib]
  ring

lemma descentMean_eq (f : ℕ → ℝ) (N : ℕ) :
    Erdos371MonotoneAdditiveReversal.descentMean f N=(descentCount f N : ℝ)/N := by
  simp only [Erdos371MonotoneAdditiveReversal.descentMean,
    Erdos371SmallPrimeAveraging.mean,sum_boole,descentCount]

/-- A restricted, genuinely uniform version of the earlier descent criterion.
It is not the criterion for all admissible functions. -/
theorem uniform_descentMean_bound {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime)
    (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ N : ℕ in atTop, ∀ (a : ℝ) (w : ℕ → ℝ), 0 ≤ a →
      Erdos371MonotoneAdditiveReversal.descentMean (height s a w) N ≤ 1/2+ε := by
  simpa only [descentMean_eq] using uniform_finite_support_bound hs ε hε

end Erdos371FiniteSupportAdditiveDescent

#print axioms Erdos371FiniteSupportAdditiveDescent.descent_ratio_bound
#print axioms Erdos371FiniteSupportAdditiveDescent.uniform_descentMean_bound
