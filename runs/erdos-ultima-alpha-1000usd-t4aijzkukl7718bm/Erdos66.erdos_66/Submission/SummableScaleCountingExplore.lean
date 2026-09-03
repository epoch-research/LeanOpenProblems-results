import Submission.CountingExplore
import Submission.SummableTailBudgetExplore

/-! A summable reciprocal-scale weight forces a set to be negligible
relative to the corresponding increasing scale. -/
namespace Erdos66SummableScaleCounting
open Filter Erdos66Counting Erdos66SummableTailBudget
open scoped Classical Topology

lemma count_div_scale_zero (E : Set ℕ) (b : ℕ → ℝ) (hb : ∀ n, 0<b n)
    (hbmono : Monotone b) (hbt : Tendsto b atTop atTop)
    (hs : Summable (fun n : ℕ ↦ if n∈E then 1/b n else 0)) :
    Tendsto (fun N ↦ (count E N : ℝ)/b N) atTop (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall (fun N ↦ ha.trans_le (div_nonneg (Nat.cast_nonneg _) (hb N).le))
  · intro ε hε
    obtain ⟨M,hM⟩ := exists_tail_budget _ hs (ε/2) (by positivity)
    have hratio := (hbt.const_div_atTop (M:ℝ)).eventually_lt_const (show (0:ℝ)<ε/2 by positivity)
    filter_upwards [hratio] with N hNratio
    let T := (cutoff E N).filter (fun n ↦ M≤n)
    have hcount : count E N ≤ M+T.card := by
      have hsub : cutoff E N ⊆ Finset.range M ∪ T := by
        intro n hn
        by_cases hm : M≤n
        · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hn,hm⟩)
        · exact Finset.mem_union_left _ (Finset.mem_range.mpr (by omega))
      exact (Finset.card_le_card hsub).trans (by
        simpa only [Finset.card_range] using Finset.card_union_le (Finset.range M) T)
    have htail := hM T (fun n hn ↦ (Finset.mem_filter.mp hn).2)
    have hmass : (T.card:ℝ) ≤ b N*(∑ n∈T, if n∈E then 1/b n else 0) := by
      rw [Finset.mul_sum]
      have hh : (∑ n∈T, (1:ℝ)) ≤ ∑ n∈T, b N*(if n∈E then 1/b n else 0) := by
        apply Finset.sum_le_sum
        intro n hn
        obtain ⟨hnE,hnM⟩ := Finset.mem_filter.mp hn
        obtain ⟨hnN,hnE⟩ := mem_cutoff.mp hnE
        rw [if_pos hnE,mul_one_div]
        exact (le_div_iff₀ (hb n)).mpr (by simpa only [one_mul] using hbmono hnN.le)
      simpa only [Finset.sum_const,nsmul_eq_mul,mul_one] using hh
    have hcountR : (count E N:ℝ)≤M+(T.card:ℝ) := by exact_mod_cast hcount
    have hmass' := hmass.trans_lt (mul_lt_mul_of_pos_left htail (hb N))
    have hMratio := (div_lt_iff₀ (hb N)).mp hNratio
    apply (div_lt_iff₀ (hb N)).mpr
    nlinarith

lemma count_div_power_zero (E : Set ℕ) (s : ℝ) (hs : 0<s)
    (hE : Summable (fun n : ℕ ↦ if n∈E then 1/((n:ℝ)+2)^s else 0)) :
    Tendsto (fun N ↦ (count E N : ℝ)/((N:ℝ)+2)^s) atTop (𝓝 0) := by
  apply count_div_scale_zero E (fun n ↦ ((n:ℝ)+2)^s)
    (fun n ↦ Real.rpow_pos_of_pos (by positivity) s) _ _ hE
  · intro m n hmn
    have hR : (m:ℝ)≤n := by exact_mod_cast hmn
    exact Real.rpow_le_rpow (by positivity) (by linarith) hs.le
  · have ht : Tendsto (fun n : ℕ ↦ (n:ℝ)+2) atTop atTop :=
      tendsto_atTop_mono (fun n ↦ by change (n:ℝ)≤(n:ℝ)+2; linarith) tendsto_natCast_atTop_atTop
    exact (tendsto_rpow_atTop hs).comp ht

end Erdos66SummableScaleCounting
