import Submission.PrefixSampling
import Submission.HypergraphHubTrimming

/-! Sampling bounds for four-uniform hypergraphs after hub trimming. -/
namespace Erdos1206.TrimmedSampling
open Finset FiniteProductSampling PrefixSampling HypergraphHubTrimming
open scoped BigOperators Classical

noncomputable def full (E : Finset (Finset ℕ)) {M k : ℕ} [NeZero k]
    (ω : Fin M → Fin k) : Finset (Finset ℕ) :=
  E.filter (fun e => ∀ v∈e, label ω v=0)

noncomputable def score (E : Finset (Finset ℕ)) (H : Finset ℕ)
    {M k : ℕ} [NeZero k] (ω : Fin M → Fin k) : ℝ :=
  ∑ e∈good E H, event (lift M (e\H)) ω

lemma full_card_le (E : Finset (Finset ℕ)) (H : Finset ℕ)
    {M k : ℕ} [NeZero k] (ω : Fin M → Fin k)
    (hM : ∀ e∈E, e ⊆ range M) :
    ((full E ω).card:ℝ) ≤ score E H ω+(bad E H).card := by
  have hpart : E=good E H ∪ bad E H := by
    ext e
    simp only [good,bad,mem_union,mem_filter]
    by_cases h : (e∩H).card ≤ 1
    · have hb : ¬2 ≤ (e∩H).card := by omega
      simp only [h,hb,and_true,and_false,or_false]
    · have hb : 2 ≤ (e∩H).card := by omega
      simp only [h,hb,and_true,and_false,false_or]
  have hfull : full E ω=full (good E H) ω ∪ full (bad E H) ω := by
    conv_lhs => rw [hpart]
    exact filter_union _ _ _
  have hg : ((full (good E H) ω).card:ℝ) ≤ score E H ω := by
    simp only [full,score,←sum_boole]
    apply sum_le_sum
    intro e he
    rw [event_lift ((sdiff_subset).trans (hM e (mem_filter.mp he).1))]
    split_ifs <;> try norm_num
    rename_i h₁ h₂
    exact h₂ (fun v hv => h₁ v (sdiff_subset hv))
  have hb : (full (bad E H) ω).card ≤ (bad E H).card := card_filter_le _ _
  have hu : (full E ω).card ≤ (full (good E H) ω).card+(full (bad E H) ω).card := by
    rw [hfull]
    exact card_union_le _ _
  have hur : ((full E ω).card:ℝ) ≤ (full (good E H) ω).card+(full (bad E H) ω).card := by
    exact_mod_cast hu
  have hbr : ((full (bad E H) ω).card:ℝ) ≤ (bad E H).card := by exact_mod_cast hb
  linarith

lemma score_mean_le (E : Finset (Finset ℕ)) (H : Finset ℕ)
    {M k : ℕ} [NeZero k]
    (hM : ∀ e∈E, e ⊆ range M) (hfour : ∀ e∈E, e.card=4) :
    (𝔼 ω : Fin M → Fin k, score E H ω) ≤ (E.card:ℝ)/(k:ℝ)^3 := by
  unfold score
  rw [expect_sum_comm]
  have hk : (1:ℝ) ≤ k := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne k)
  have hp : 1/(k:ℝ) ≤ 1 := (div_le_one (by positivity : (0:ℝ) < k)).mpr hk
  calc
    _ ≤ ∑ _e∈good E H, (1/(k:ℝ))^3 := by
      apply sum_le_sum
      intro e he
      rw [event_mean,lift_card (sdiff_subset.trans (hM e (mem_filter.mp he).1))]
      exact pow_le_pow_of_le_one (by positivity) hp (good_support_size he (hfour e (mem_filter.mp he).1)).1
    _ = ((good E H).card:ℝ)/(k:ℝ)^3 := by simp [div_eq_mul_inv]
    _ ≤ (E.card:ℝ)/(k:ℝ)^3 := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact_mod_cast card_filter_le E (fun e => (e∩H).card ≤ 1)

lemma score_centered (E : Finset (Finset ℕ)) (H : Finset ℕ)
    {M k : ℕ} [NeZero k] (ω : Fin M → Fin k) :
    score E H ω-(𝔼 η : Fin M → Fin k, score E H η)=
      ∑ e∈good E H, centered (lift M (e\H)) ω := by
  unfold score centered
  rw [expect_sum_comm,←sum_sub_distrib]
  simp only [event_mean]

lemma score_variance (E : Finset (Finset ℕ)) (D : ℕ)
    {M k : ℕ} [NeZero k] (hfour : ∀ e∈E, e.card=4) :
    (𝔼 ω : Fin M → Fin k,
      (score E (hubs E D) ω-(𝔼 η : Fin M → Fin k, score E (hubs E D) η))^2)
      ≤ (E.card:ℝ)*4*D := by
  simp_rw [score_centered]
  have hh := family_variance (M := M) (k := k) (r := 4) (D := D)
    (good E (hubs E D)) (fun e => e\hubs E D)
    (fun e he => (good_support_size he (hfour e (mem_filter.mp he).1)).2)
    (good_degree_le E D)
  apply hh.trans
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  apply mul_le_mul_of_nonneg_right _ (by norm_num)
  exact_mod_cast card_filter_le E (fun e => (e∩hubs E D).card ≤ 1)

#print axioms full_card_le
#print axioms score_mean_le
#print axioms score_variance
end Erdos1206.TrimmedSampling
