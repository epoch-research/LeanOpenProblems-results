import Submission.BoundaryCorrectionEligibilityExplore

/-! Exact upper-endpoint demand for central clipping. Rank restoration no
longer needs a midpoint exclusion margin. -/
namespace Erdos66ExactClippingDemand
open AdditiveCombinatorics Erdos66BoundaryCorrectionEligibility
  Erdos66BoundaryPairCounts Erdos66CentralTripleDeletion
open scoped Classical
set_option maxHeartbeats 1500000

def clipDemand (r q : ℕ) : ℕ := (r-q+1)/2

lemma clipDemand_eq_zero_iff (r q : ℕ) : clipDemand r q=0 ↔ r ≤ q := by
  unfold clipDemand
  omega

lemma clipDemand_le (r q : ℕ) : clipDemand r q ≤ r := by
  unfold clipDemand
  omega

/-- The chosen set has exactly the ceiling of half the positive excess.
Only the central boundary margin is needed; there is no host bracket
hypothesis in this cardinal selection. -/
theorem exists_central_clipping_exact (A : Set ℕ) (d n q : ℕ) (hd : 2 ≤ d)
    (hq : 2*(boundary A d n).card+2 ≤ q) :
    ∃ D : Finset ℕ, D ⊆ upperEndpoints A (n/d^2) n ∧
      D.card=clipDemand (sumRep A n) q ∧
      sumRep A n-2*D.card ≤ q ∧
      min (sumRep A n) (q-1) ≤ sumRep A n-2*D.card := by
  have hcap := central_capacity A d n hd
  have hk : clipDemand (sumRep A n) q ≤ (upperEndpoints A (n/d^2) n).card := by
    unfold clipDemand
    omega
  obtain ⟨D,hD,hcard⟩ := Finset.exists_subset_card_eq hk
  refine ⟨D,hD,hcard,?_,?_⟩ <;> unfold clipDemand at hcard <;> omega

end Erdos66ExactClippingDemand
