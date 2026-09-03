import Submission.BuchstabLevelMonotonicity

/-! Exact density-centered formulas for the two main-term refinement steps.
No approximation of a prime sum is made in these identities. -/
namespace Erdos970.RecursiveSieve.Buchstab
open Finset
open scoped Classical

lemma lowerStep_density_identity (q : ℕ → ℝ) (keep : ℕ → ℝ → Prop)
    (U : ℕ → ℝ → ℝ) (k : ℕ) (D : ℝ) :
    lowerStep q keep U k D = if keep k D then
      max 0 (prefixDensity q k-∑ i : Fin k, q i.val*(U i.val (D*q i.val)-prefixDensity q i.val)) else 0 := by
  classical
  have he : prefixDensity q k-(∑ i : Fin k, q i.val*(U i.val (D*q i.val)-prefixDensity q i.val)) =
      1-∑ i : Fin k, q i.val*U i.val (D*q i.val) := by
    rw [prefixDensity_first_hit]
    simp_rw [mul_sub]
    rw [sum_sub_distrib]
    ring
  simp only [lowerStep, he]

lemma upperMain_density_identity (q : ℕ → ℝ) (keep : ℕ → ℝ → Prop)
    (base : ℕ → ℝ → ℝ) (n k : ℕ) (D : ℝ) :
    upperMain q keep base (n+1) k D = min (upperMain q keep base n k D)
      (prefixDensity q k+∑ i : Fin k, q i.val*(prefixDensity q i.val-
        lowerStep q keep (upperMain q keep base n) i.val (D*q i.val))) := by
  have he : prefixDensity q k+(∑ i : Fin k, q i.val*(prefixDensity q i.val-
      lowerStep q keep (upperMain q keep base n) i.val (D*q i.val))) =
      1-∑ i : Fin k, q i.val*lowerStep q keep (upperMain q keep base n) i.val (D*q i.val) := by
    rw [prefixDensity_first_hit]
    simp_rw [mul_sub]
    rw [sum_sub_distrib]
    ring
  simp only [upperMain, he]

/-- An upper bound on total excess gives a lower main bound. The cutoff
premise is essential and is not replaced by the positivity of a model profile. -/
lemma lowerStep_ge_of_excess (q : ℕ → ℝ) (keep : ℕ → ℝ → Prop)
    (U : ℕ → ℝ → ℝ) (k : ℕ) (D l : ℝ) (hk : keep k D)
    (h : (∑ i : Fin k, q i.val*(U i.val (D*q i.val)-prefixDensity q i.val)) ≤
      prefixDensity q k*(1-l)) :
    prefixDensity q k*l ≤ lowerStep q keep U k D := by
  rw [lowerStep_density_identity, if_pos hk]
  apply le_trans _ (le_max_right _ _)
  nlinarith only [h]

/-- An upper bound on the lower-child deficit gives a new upper main bound. -/
lemma upperMain_le_of_deficit (q : ℕ → ℝ) (keep : ℕ → ℝ → Prop)
    (base : ℕ → ℝ → ℝ) (n k : ℕ) (D u : ℝ)
    (h : (∑ i : Fin k, q i.val*(prefixDensity q i.val-
      lowerStep q keep (upperMain q keep base n) i.val (D*q i.val))) ≤ prefixDensity q k*(u-1)) :
    upperMain q keep base (n+1) k D ≤ prefixDensity q k*u := by
  rw [upperMain_density_identity]
  apply (min_le_right _ _).trans
  nlinarith only [h]

#print axioms lowerStep_ge_of_excess
#print axioms upperMain_le_of_deficit
end Erdos970.RecursiveSieve.Buchstab
