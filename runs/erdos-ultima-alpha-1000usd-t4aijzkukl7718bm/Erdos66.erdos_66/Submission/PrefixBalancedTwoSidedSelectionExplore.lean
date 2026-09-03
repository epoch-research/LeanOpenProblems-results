import Submission.CompensatedPipageExplore

/-! Finite exponential selection for either sign of the tilt, retaining all
prefix brackets. The penalty is uniform in the number of coordinates. -/
namespace Erdos66PrefixBalancedTwoSidedSelection
open AdditiveCombinatorics Erdos66FiniteBernoulli Erdos66FiniteRepBernoulli
  Erdos66OrderedPipagePrefix Erdos66PrefixBalancedUpperSelection Erdos66CompensatedPipage
open scoped Classical

 theorem exists_prefix_balanced_selection {κ : Type*} (L : ℕ)
    (p : Fin (L+1) → ℝ) (hp : ∀ i, 0≤p i ∧ p i≤1)
    (T : Finset κ) (n : κ → ℕ) (t w : κ → ℝ) (hw : ∀ k∈T, 0≤w k) :
    ∃ ω : Fin (L+1) → Bool,
      Brackets p (fun i ↦ bit (ω i)) ∧
      (∑ k∈T, w k*Real.exp (t k*(sumRep (selected L ω) (n k) : ℝ)))≤
        ∑ k∈T, w k*(Real.exp (2*|t k|)*expect p
          (fun σ ↦ Real.exp (t k*(sumRep (selected L σ) (n k) : ℝ)))) := by
  obtain ⟨y,hy,hbr,hcost⟩ := exists_compensated_rounding L T n t w hw p hp
  let ω : Fin (L+1) → Bool := fun i ↦ decide (y i=1)
  have he : (fun i ↦ bit (ω i))=y := by
    funext i
    rcases hy i with hi | hi <;> simp [ω,bit,hi]
  refine ⟨ω,by simpa only [he] using hbr,?_⟩
  rw [←he] at hcost
  simpa only [expPoly_eq_expect,expect_pure] using hcost

end Erdos66PrefixBalancedTwoSidedSelection
