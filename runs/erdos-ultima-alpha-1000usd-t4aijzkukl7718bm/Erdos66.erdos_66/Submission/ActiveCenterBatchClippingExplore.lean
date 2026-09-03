import Submission.NaturalScaleBatchClippingExplore

/-! Only centers actually above their requested cap contribute to demand,
boundary requirements, and cross-incidence. -/
namespace Erdos66ActiveCenterBatchClipping
open Filter AdditiveCombinatorics Erdos66NaturalScaleBatchClipping
  Erdos66ExactClippingDemand Erdos66ClampedPrefixContinuation Erdos66Fractional
  Erdos66CentralTripleCounts Erdos66BoundaryPairCounts Erdos66OrderedPartialReplacement
open scoped Classical Topology
set_option maxHeartbeats 3500000

noncomputable def activeCenters (A : Set ℕ) (T : Finset ℕ) (q : ℕ → ℕ) : Finset ℕ :=
  T.filter (fun n ↦ q n < sumRep A n)

lemma active_demand (A : Set ℕ) (T : Finset ℕ) (q : ℕ → ℕ) :
    (∑ n∈activeCenters A T q, (clipDemand (sumRep A n) (q n) : ℝ)) =
      ∑ n∈T, (clipDemand (sumRep A n) (q n) : ℝ) := by
  rw [activeCenters,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n _
  by_cases hn : q n < sumRep A n
  · simp only [hn,if_true]
  · rw [if_neg hn,(clipDemand_eq_zero_iff _ _).mpr (by omega),Nat.cast_zero]

 theorem uniformly_eventually_active_clipping
    (S : ℕ → ℝ) (hS : ∀ᶠ N in atTop, 0 ≤ S N)
    (hdec : Tendsto (fun N : ℕ ↦ S N/Real.sqrt ((N : ℝ)*Real.log N)) atTop (𝓝 0))
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ A : Set ℕ,
      (∀ L, PrefixBrackets profile A L) →
      ∀ (T : Finset ℕ) (d q : ℕ → ℕ),
      (∑ n∈T, (clipDemand (sumRep A n) (q n) : ℝ)) ≤ S N →
      (∀ z, z ≤ N^33 →
        2*(∑ n∈(activeCenters A T q).erase z,
          ((fiber A (n/(d n)^2) n z).card : ℝ)) ≤ (ε/2)*Real.log N) →
      (∀ n∈activeCenters A T q, 2 ≤ d n ∧ 4*N ≤ n ∧ n ≤ 5*N) →
      (∀ n∈activeCenters A T q, 2*(boundary A (d n) n).card+2 ≤ q n) →
      ∃ D F : Finset ℕ, F.card=D.card ∧ Disjoint (F : Set ℕ) A ∧
        (∀ u∈D∪F, N ≤ u ∧ u ≤ 6*N) ∧
        (∀ L, PrefixBrackets profile (swap A D F) L) ∧
        (∀ n∈T, ((min (sumRep A n) (q n-1) : ℕ) : ℝ) ≤
            sumRep (swap A D F) n+ε*Real.log ((n : ℝ)+2) ∧
          (sumRep (swap A D F) n : ℝ) ≤ q n+ε*Real.log ((n : ℝ)+2)) ∧
        ∀ z, z∉activeCenters A T q →
          |(sumRep (swap A D F) z : ℝ)-sumRep A z| ≤ ε*Real.log ((z : ℝ)+2) := by
  filter_upwards [uniformly_eventually_batch_downward_clipping S hS hdec ε hε] with N hN
  intro A hbr T d q hdemand hcross hloc hq
  have hdemand' : (∑ n∈activeCenters A T q, (clipDemand (sumRep A n) (q n) : ℝ)) ≤ S N := by
    rw [active_demand]
    exact hdemand
  obtain ⟨D,F,hcard,hFA,hs,hbr',hclip,hother⟩ :=
    hN A hbr (activeCenters A T q) d q hdemand' hcross hloc hq
  refine ⟨D,F,hcard,hFA,hs,hbr',?_,hother⟩
  intro n hn
  by_cases ha : n∈activeCenters A T q
  · exact hclip n ha
  · have hnot : sumRep A n ≤ q n := by
      by_contra hh
      exact ha (Finset.mem_filter.mpr ⟨hn,by omega⟩)
    have herr := abs_le.mp (hother n ha)
    have hlo : ((min (sumRep A n) (q n-1) : ℕ) : ℝ) ≤ sumRep A n := by
      exact_mod_cast min_le_left (sumRep A n) (q n-1)
    have hhi : (sumRep A n : ℝ) ≤ q n := by exact_mod_cast hnot
    constructor <;> linarith

end Erdos66ActiveCenterBatchClipping
