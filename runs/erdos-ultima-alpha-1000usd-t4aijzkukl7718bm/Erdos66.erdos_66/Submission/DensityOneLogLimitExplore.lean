import Submission.HarmonicExceptionalProfileExplore
import Submission.SummableExceptionalSetExplore
import Submission.CountingExplore

/-! A fixed logarithmic representation limit outside a density-zero,
harmonically summable exceptional set. Not an everywhere limit. -/
namespace Erdos66DensityOneLogLimit
open Filter AdditiveCombinatorics Erdos66Counting Erdos66SummableTailBudget
  Erdos66HarmonicExceptionalProfile Erdos66SummableExceptionalSet
open scoped Classical Topology
set_option maxHeartbeats 1500000

lemma density_zero_of_harmonic_summable (E : Set ℕ)
    (hs : Summable (fun n : ℕ ↦ if n∈E then 1/((n:ℝ)+2) else 0)) :
    Tendsto (fun N ↦ (count E N : ℝ)/N) atTop (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall (fun N ↦ ha.trans_le (by positivity))
  · intro ε hε
    obtain ⟨M,hM⟩ := exists_tail_budget _ hs (ε/4) (by positivity)
    have hratio := ((tendsto_natCast_atTop_atTop (R := ℝ)).const_div_atTop (M:ℝ)).eventually_lt_const
      (show (0:ℝ)<ε/2 by positivity)
    filter_upwards [hratio,eventually_ge_atTop 2] with N hNratio hN2
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
    have hmass : (T.card:ℝ) ≤ ((N:ℝ)+2)*
        (∑ n∈T, if n∈E then 1/((n:ℝ)+2) else 0) := by
      rw [Finset.mul_sum]
      have hh : (∑ n∈T, (1:ℝ)) ≤ ∑ n∈T, ((N:ℝ)+2)*
          (if n∈E then 1/((n:ℝ)+2) else 0) := by
        apply Finset.sum_le_sum
        intro n hn
        obtain ⟨hnE,hnM⟩ := Finset.mem_filter.mp hn
        obtain ⟨hnN,hnE⟩ := mem_cutoff.mp hnE
        rw [if_pos hnE,mul_one_div]
        apply (le_div_iff₀ (by positivity : 0<(n:ℝ)+2)).mpr
        have hh : (n:ℝ)≤N := by exact_mod_cast hnN.le
        linarith
      simpa only [Finset.sum_const,nsmul_eq_mul,mul_one,Nat.cast_id] using hh
    have hNp : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
    have hN2R : (2:ℝ)≤N := by exact_mod_cast hN2
    have hcountR : (count E N:ℝ)≤M+(T.card:ℝ) := by exact_mod_cast hcount
    have hmass' := hmass.trans_lt (mul_lt_mul_of_pos_left htail (by positivity : 0<(N:ℝ)+2))
    have hMratio := (div_lt_iff₀ hNp).mp hNratio
    apply (div_lt_iff₀ hNp).mpr
    nlinarith

/-- Every positive coefficient is attainable outside one harmonically
summable exceptional set, which necessarily has natural density zero. -/
theorem exists_log_limit_off_summable_exception (c : ℝ) (hc : 0<c) :
    ∃ A E : Set ℕ,
      Summable (fun n : ℕ ↦ if n∈E then 1/((n:ℝ)+2) else 0) ∧
      Tendsto (fun N ↦ (count E N : ℝ)/N) atTop (𝓝 0) ∧
      Tendsto (fun n ↦ if n∈E then c else (sumRep A n : ℝ)/Real.log n) atTop (𝓝 c) := by
  obtain ⟨A,hA⟩ := exists_harmonically_summable_exceptions c hc
  obtain ⟨E,hE,hlim⟩ := exists_exceptional_set
    (fun n ↦ (sumRep A n : ℝ)/Real.log n) c (fun n ↦ 1/((n:ℝ)+2))
    (fun n ↦ by positivity) hA
  exact ⟨A,E,hE,density_zero_of_harmonic_summable E hE,hlim⟩

end Erdos66DensityOneLogLimit
