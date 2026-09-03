import Submission.NaturalScaleBracketRestorationExplore
import Submission.BatchCentralDeletionExplore
import Submission.ExactClippingDemandExplore

/-! Batch clipping with actual half-excess demand and aggregate cross-incidence.
No cardinality bound on the center set or global representation envelope is assumed. -/
namespace Erdos66NaturalScaleBatchClipping
open Filter AdditiveCombinatorics Erdos66NaturalScaleBracketRestoration
  Erdos66BatchCentralDeletion Erdos66ExactClippingDemand Erdos66BoundaryCorrectionEligibility
  Erdos66ClampedPrefixContinuation Erdos66Fractional Erdos66CentralTripleDeletion
  Erdos66CentralTripleCounts Erdos66BoundaryPairCounts Erdos66OrderedPartialReplacement
  Erdos66LogCellWindowBudget Erdos66PredecessorScaleBudget Erdos66PredecessorCutoffTransfer
  Erdos66ShortSupportSwapTail Erdos66Explore Erdos66Compactness
open scoped Classical Topology
set_option maxHeartbeats 6000000
set_option linter.style.existsImplication false

theorem uniformly_eventually_batch_downward_clipping
    (S : ℕ → ℝ) (hS : ∀ᶠ N in atTop, 0 ≤ S N)
    (hdec : Tendsto (fun N : ℕ ↦ S N/Real.sqrt ((N : ℝ)*Real.log N)) atTop (𝓝 0))
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ A : Set ℕ,
      (∀ L, PrefixBrackets profile A L) →
      ∀ (T : Finset ℕ) (d q : ℕ → ℕ),
      (∑ n∈T, (clipDemand (sumRep A n) (q n) : ℝ)) ≤ S N →
      (∀ z, z ≤ N^33 →
        2*(∑ n∈T.erase z, ((fiber A (n/(d n)^2) n z).card : ℝ)) ≤ (ε/2)*Real.log N) →
      (∀ n∈T, 2 ≤ d n ∧ 4*N ≤ n ∧ n ≤ 5*N) →
      (∀ n∈T, 2*(boundary A (d n) n).card+2 ≤ q n) →
      ∃ D F : Finset ℕ, F.card=D.card ∧ Disjoint (F : Set ℕ) A ∧
        (∀ u∈D∪F, N ≤ u ∧ u ≤ 6*N) ∧
        (∀ L, PrefixBrackets profile (swap A D F) L) ∧
        (∀ n∈T, ((min (sumRep A n) (q n-1) : ℕ) : ℝ) ≤
            sumRep (swap A D F) n+ε*Real.log ((n : ℝ)+2) ∧
          (sumRep (swap A D F) n : ℝ) ≤ q n+ε*Real.log ((n : ℝ)+2)) ∧
        ∀ z, z∉T → |(sumRep (swap A D F) z : ℝ)-sumRep A z| ≤ ε*Real.log ((z : ℝ)+2) := by
  have hlog : Tendsto (fun N : ℕ ↦ Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [uniformly_eventually_rank_restoration S hS hdec (ε/2) (by positivity),
    eventually_ge_atTop 32,hlog.eventually_ge_atTop 1,
    eventually_harmonic_short_support_tail,hlog.eventually_ge_atTop (6/ε)]
    with N hrestore hN hl htail hl6
  intro A hbr T d q hdemand hbudget hloc hq
  have hchoices (n : ℕ) : ∃ E : Finset ℕ, n∈T →
      E ⊆ upperEndpoints A (n/(d n)^2) n ∧
      E.card=clipDemand (sumRep A n) (q n) ∧
      sumRep A n-2*E.card ≤ q n ∧ min (sumRep A n) (q n-1) ≤ sumRep A n-2*E.card := by
    by_cases hn : n∈T
    · obtain ⟨E,hE⟩ := exists_central_clipping_exact A (d n) n (q n) (hloc n hn).1 (hq n hn)
      exact ⟨E,fun _ ↦ hE⟩
    · exact ⟨∅,fun hh ↦ (hn hh).elim⟩
  choose E hE using hchoices
  let D := T.biUnion E
  have hDU (n : ℕ) (hn : n∈T) : E n ⊆ upperEndpoints A (n/(d n)^2) n := (hE n hn).1
  have hDE (n : ℕ) (hn : n∈T) : E n ⊆ endpoints A (n/(d n)^2) n :=
    (hDU n hn).trans (Finset.filter_subset _ _)
  have hDA : (D : Set ℕ) ⊆ A := by
    intro a ha
    obtain ⟨n,hn,ha⟩ := Finset.mem_biUnion.mp ha
    exact (mem_upperEndpoints.mp (hDU n hn ha)).2.2.2.1
  have hDloc (a : ℕ) (ha : a∈D) : 2*N ≤ a ∧ a ≤ 5*N := by
    obtain ⟨n,hn,ha⟩ := Finset.mem_biUnion.mp ha
    have he := mem_upperEndpoints.mp (hDU n hn ha)
    have hh := hloc n hn
    omega
  have hXX : 5*N < N^33+1 := by
    have hp := Nat.pow_le_pow_right (by omega : 0 < N) (show 2 ≤ 33 by norm_num)
    have hh : 5*N ≤ N^2 := by nlinarith
    omega
  have hcard : (D.card : ℝ) ≤ S N := by
    have hc : (D.card : ℝ) ≤ ∑ n∈T, ((E n).card : ℝ) := by
      exact_mod_cast (Finset.card_biUnion_le : (T.biUnion E).card ≤ ∑ n∈T, (E n).card)
    have he : (∑ n∈T, ((E n).card : ℝ)) = ∑ n∈T, (clipDemand (sumRep A n) (q n) : ℝ) :=
      Finset.sum_congr rfl (fun n hn ↦ by rw [(hE n hn).2.1])
    exact hc.trans (he.le.trans hdemand)
  obtain ⟨F,hFc,hFA,hs,hbr',hrest⟩ := hrestore A hbr D hDA hDloc hcard
  have hlogpos (z : ℕ) : 0 ≤ Real.log ((z : ℝ)+2) :=
    Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) z; linarith)
  have hlogge (z : ℕ) (hz : N ≤ z) : Real.log (N : ℝ) ≤ Real.log ((z : ℝ)+2) :=
    Real.log_le_log (by exact_mod_cast (by omega : 0 < N)) (by exact_mod_cast (by omega : N ≤ z+2))
  refine ⟨D,F,hFc,hFA,hs,hbr',?_,?_⟩
  · intro n hn
    have hnhi := (hloc n hn).2.2
    have hnlo := (hloc n hn).2.1
    obtain ⟨hcorehi,hcorelo⟩ := center_core_bounds A T (fun n ↦ n/(d n)^2) E hDU n hn
    have hsum' := hbudget n (by omega)
    have hcliphi := (hE n hn).2.2.1
    have hcliplo := (hE n hn).2.2.2
    have hhlo : min (sumRep A n) (q n-1) ≤ sumRep (A\(D : Set ℕ)) n+2*(∑ j∈T.erase n, (fiber A (j/(d j)^2) j n).card) := by
      change sumRep (A\(D : Set ℕ)) n ≤ _ at hcorehi
      change _ ≤ sumRep (A\(D : Set ℕ)) n+_ at hcorelo
      omega
    have hhhi : sumRep (A\(D : Set ℕ)) n ≤ q n := hcorehi.trans hcliphi
    have hhloR : ((min (sumRep A n) (q n-1) : ℕ) : ℝ) ≤
        sumRep (A\(D : Set ℕ)) n+2*(∑ j∈T.erase n, ((fiber A (j/(d j)^2) j n).card : ℝ)) := by exact_mod_cast hhlo
    have hhhiR : (sumRep (A\(D : Set ℕ)) n : ℝ) ≤ q n := by exact_mod_cast hhhi
    have hmonR : (sumRep (A\(D : Set ℕ)) n : ℝ) ≤ sumRep (swap A D F) n :=
      by exact_mod_cast (hrest n).1
    have hload := (hrest n).2
    have hscale := mul_le_mul_of_nonneg_left (hlogge n (by omega)) (show 0 ≤ ε/2 by positivity)
    have hp := mul_nonneg hε.le (hlogpos n)
    constructor <;> nlinarith
  · intro z hzT
    by_cases hzlo : z<N
    · have he : sumRep (swap A D F) z=sumRep A z := by
        apply sumRep_congr_below
        intro a ha
        apply swap_mem_outside
        intro hh
        have := (hs a hh).1
        omega
      rw [he,sub_self,abs_zero]
      exact mul_nonneg hε.le (hlogpos z)
    · by_cases hz : z ≤ N^33
      · have hdel := union_deletion_loss A T (fun n ↦ n/(d n)^2) E hDE z
        change sumRep A z ≤ sumRep (A\(D : Set ℕ)) z+_ at hdel
        have hsum' := hbudget z hz
        rw [Finset.erase_eq_of_notMem hzT] at hsum'
        have hdelR : (sumRep A z : ℝ) ≤ sumRep (A\(D : Set ℕ)) z+
            2*(∑ n∈T, ((fiber A (n/(d n)^2) n z).card : ℝ)) := by
          exact_mod_cast hdel
        have hcoreR : (sumRep (A\(D : Set ℕ)) z : ℝ) ≤ sumRep A z :=
          by exact_mod_cast sumRep_mono (show A\(D : Set ℕ) ⊆ A from Set.diff_subset) z
        have hmonR : (sumRep (A\(D : Set ℕ)) z : ℝ) ≤ sumRep (swap A D F) z :=
          by exact_mod_cast (hrest z).1
        have hload := (hrest z).2
        have hscale := mul_le_mul_of_nonneg_left (hlogge z (by omega)) (show 0 ≤ ε/2 by positivity)
        have hp := mul_nonneg hε.le (hlogpos z)
        rw [abs_le]
        constructor <;> nlinarith
      · have hh := htail A hbr D F hDA hFA
          (fun a ha ↦ by have := (hs a ha).2; omega) z (by omega)
        have h6 : 6 ≤ ε*Real.log N := by
          have h := (div_le_iff₀ hε).mp hl6
          nlinarith
        have hscale := mul_le_mul_of_nonneg_left (hlogge z (by omega)) hε.le
        linarith

end Erdos66NaturalScaleBatchClipping
