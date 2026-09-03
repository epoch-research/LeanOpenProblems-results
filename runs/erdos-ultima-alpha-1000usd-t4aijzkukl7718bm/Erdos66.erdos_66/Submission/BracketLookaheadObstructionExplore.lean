import Submission.ExactBracketPeaksExplore

/-! Exact prefix brackets do not alone ensure a feasible next-target upper
bound. The counterexample is a specially chosen prefix, not every prefix. -/
namespace Erdos66BracketLookaheadObstruction
open Filter AdditiveCombinatorics Erdos66Generating Erdos66Counting
  Erdos66ClampedPrefixContinuation Erdos66ExactBracketPeaks Erdos66Fractional
  Erdos66Explore Erdos66Compactness
open scoped Classical Topology
set_option maxHeartbeats 1800000

lemma last_cutoff_loss (A : Set ℕ) (n : ℕ) :
    sumRep A n≤ sumRep (cutoff A n:Set ℕ) n+2 := by
  have hsub : A⊆insert n (A\{n}) := by
    intro i hi
    by_cases hin : i=n
    · exact Or.inl hin
    · exact Or.inr ⟨hi,by simpa only [Set.mem_singleton_iff] using hin⟩
  have he : sumRep (A\{n}) n=sumRep (cutoff A n:Set ℕ) n := by
    apply sumRep_congr_below
    intro i hi
    simp only [Set.mem_diff,Set.mem_singleton_iff,Finset.mem_coe,mem_cutoff]
    constructor
    · rintro ⟨hA,hne⟩
      exact ⟨by omega,hA⟩
    · rintro ⟨hin,hA⟩
      exact ⟨hA,by omega⟩
  have hh := (sumRep_mono hsub n).trans (sumRep_insert_le (A\{n}) n n)
  simpa only [he] using hh

lemma cutoff_mass (A : Set ℕ) (N k : ℕ) (hk : k≤ N) :
    mass (indicator (cutoff A N:Set ℕ)) k=mass (indicator A) k := by
  apply Finset.sum_congr rfl
  intro i hi
  have hiN : i<N := by have := Finset.mem_range.mp hi; omega
  simp only [indicator,Finset.mem_coe,mem_cutoff,hiN,true_and]

/-- An arbitrarily late prefix can satisfy every exact original bracket and
have a large representation count at the VERY NEXT target already forced
by its old points. No extension above the cutoff can remove that peak. -/
theorem exists_exact_bracket_prefix_forcing_peak (R : ℝ) (N₀ : ℕ) :
    ∃ N : ℕ, N₀≤ N ∧ 2≤ N ∧ ∃ C : Finset ℕ,
      C⊆Finset.range N ∧ PrefixBrackets profile (C:Set ℕ) N ∧
      (∀ k≤ N, |mass (indicator (C:Set ℕ)) k-mass profile k|≤ 3/4) ∧
      ∀ B : Set ℕ, (C:Set ℕ)⊆B → R<(sumRep B N:ℝ)/Real.log N := by
  have hloglim : Tendsto (fun n : ℕ ↦ Real.log (n:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨L,hL⟩ := eventually_atTop.mp (hloglim.eventually_ge_atTop 2)
  obtain ⟨M,hM⟩ := exists_nat_gt (R+1)
  obtain ⟨N,hN,hpeak⟩ := badSet_peaks M (max N₀ (max L 2))
  have hN0 : N₀≤ N := by omega
  have hN2 : 2≤ N := by omega
  have hl : 2≤ Real.log (N:ℝ) := hL N (by omega)
  have hlp : 0<Real.log (N:ℝ) := by linarith
  let C := cutoff badSet N
  have hC : C⊆Finset.range N := Finset.filter_subset _ _
  have hbr : PrefixBrackets profile (C:Set ℕ) N := by
    intro k hk
    rw [cutoff_mass badSet N k hk]
    exact badSet_brackets N k hk
  have hdisc : ∀ k≤ N, |mass (indicator (C:Set ℕ)) k-mass profile k|≤ 3/4 := by
    intro k hk
    rw [cutoff_mass badSet N k hk]
    exact badSet_mass_discrepancy k
  have hlarge : R<(sumRep (C:Set ℕ) N:ℝ)/Real.log N := by
    have hh : (sumRep badSet N:ℝ)≤ (sumRep (C:Set ℕ) N:ℝ)+2 := by
      exact_mod_cast last_cutoff_loss badSet N
    have hp := (le_div_iff₀ hlp).mp hpeak
    have hm := mul_lt_mul_of_pos_right hM hlp
    apply (lt_div_iff₀ hlp).mpr
    nlinarith
  refine ⟨N,hN0,hN2,C,hC,hbr,hdisc,fun B hCB ↦ ?_⟩
  have hh : (sumRep (C:Set ℕ) N:ℝ)≤ sumRep B N := by exact_mod_cast sumRep_mono hCB N
  exact hlarge.trans_le (div_le_div_of_nonneg_right hh hlp.le)

end Erdos66BracketLookaheadObstruction
