import Submission.BernoulliMatchingPolynomialExplore

/-! Joint ordered selection for positive matching-polynomial penalties and
compensated two-sided representation costs. -/
namespace Erdos66MatchingPolynomialSelection
open Erdos66FiniteBernoulli Erdos66FiniteRepBernoulli Erdos66OrderedPositiveRounding
  Erdos66OrderedPipagePrefix Erdos66PositiveBinaryExpansion
  Erdos66BernoulliMatchingPolynomial Erdos66MatchingPartition AdditiveCombinatorics
open scoped Classical
set_option maxHeartbeats 2400000

 theorem exists_matching_poly_selection {α β κ : Type*} (L : ℕ)
    (U : Finset α) (S : α → Finset β) (E : α → β → Finset (Fin (L+1)))
    (s a : α → ℝ) (hs : ∀ k∈U, 0≤s k) (ha : ∀ k∈U, 0≤a k)
    (T : Finset κ) (n : κ → ℕ) (t w : κ → ℝ) (hw : ∀ k∈T, 0≤w k)
    (p : Fin (L+1) → ℝ) (hp : ∀ i, 0≤p i ∧ p i≤1) :
    ∃ ω : Fin (L+1) → Bool, Brackets p (fun i ↦ bit (ω i)) ∧
      (∑ k∈U, a k*matchingPoly (S k) (E k) (s k) (fun i ↦ bit (ω i)))+
      (∑ k∈T, w k*Real.exp (t k*(sumRep (selected L ω) (n k) : ℝ)))≤
        (∑ k∈U, a k*matchingPoly (S k) (E k) (s k) p)+
        ∑ k∈T, w k*(Real.exp (2*|t k|)*expect p
          (fun σ ↦ Real.exp (t k*(sumRep (selected L σ) (n k) : ℝ)))) := by
  let Q : Finset (Σ _k : α, Finset β) := U.sigma (fun k ↦ matchings (S k) (E k))
  let c : (Σ _k : α, Finset β) → ℝ := fun z ↦ a z.1*(Real.exp (s z.1)-1)^z.2.card
  let F : (Σ _k : α, Finset β) → Finset (Fin (L+1)) := fun z ↦ z.2.biUnion (E z.1)
  have hc : ∀ z∈Q, 0≤c z := by
    intro z hz
    obtain ⟨hk,hM⟩ := Finset.mem_sigma.mp hz
    exact mul_nonneg (ha z.1 hk) (pow_nonneg (sub_nonneg.mpr (Real.one_le_exp (hs z.1 hk))) _)
  have hpoly (x : Fin (L+1) → ℝ) : poly Q c F x =
      ∑ k∈U, a k*matchingPoly (S k) (E k) (s k) x := by
    simp only [poly,Q,c,F,Finset.sum_sigma,matchingPoly,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    apply Finset.sum_congr (by ext M; simp [matchings])
    intro M hM
    rw [mul_assoc]
    congr 2
    apply Finset.prod_congr
    · ext i; simp
    · intro i hi; rfl
  obtain ⟨ω,hbr,hcost⟩ := exists_combined_selection L Q c F hc T n t w hw p hp
  refine ⟨ω,hbr,?_⟩
  simpa only [hpoly,expect_sum,expect_const_mul,matchingPoly_expect] using hcost

end Erdos66MatchingPolynomialSelection
