import Submission.PositiveBinaryExpansionExplore

/-! Joint finite selection for arbitrary positive exponential monomial costs
and two-sided representation potentials, with all prefix brackets retained. -/
namespace Erdos66MixedExponentialSelection
open Erdos66FiniteBernoulli Erdos66FiniteRepBernoulli Erdos66OrderedPositiveRounding
  Erdos66OrderedPipagePrefix Erdos66PositiveBinaryExpansion AdditiveCombinatorics
open scoped Classical
set_option maxHeartbeats 2200000

 theorem exists_mixed_exponential_selection {α β κ : Type*} (L : ℕ)
    (U : Finset α) (S : α → Finset β) (E : α → β → Finset (Fin (L+1)))
    (v : α → β → ℝ) (s a : α → ℝ)
    (hv : ∀ k∈U, ∀ b∈S k, 0≤v k b) (hs : ∀ k∈U, 0≤s k) (ha : ∀ k∈U, 0≤a k)
    (T : Finset κ) (n : κ → ℕ) (t w : κ → ℝ) (hw : ∀ k∈T, 0≤w k)
    (p : Fin (L+1) → ℝ) (hp : ∀ i, 0≤p i ∧ p i≤1) :
    ∃ ω : Fin (L+1) → Bool, Brackets p (fun i ↦ bit (ω i)) ∧
      (∑ k∈U, a k*Real.exp (s k*∑ b∈S k, v k b*monomial (E k b) ω))+
      (∑ k∈T, w k*Real.exp (t k*(sumRep (selected L ω) (n k) : ℝ)))≤
        expect p (fun σ ↦ ∑ k∈U, a k*Real.exp (s k*∑ b∈S k, v k b*monomial (E k b) σ))+
        ∑ k∈T, w k*(Real.exp (2*|t k|)*expect p
          (fun σ ↦ Real.exp (t k*(sumRep (selected L σ) (n k) : ℝ)))) := by
  let Q : Finset (Σ _k : α, Finset β) := U.sigma (fun k ↦ (S k).powerset)
  let c : (Σ _k : α, Finset β) → ℝ := fun z ↦ a z.1*∏ b∈z.2, (Real.exp (s z.1*v z.1 b)-1)
  let F : (Σ _k : α, Finset β) → Finset (Fin (L+1)) := fun z ↦ z.2.biUnion (E z.1)
  have hc : ∀ z∈Q, 0≤c z := by
    intro z hz
    obtain ⟨hk,hS⟩ := Finset.mem_sigma.mp hz
    exact mul_nonneg (ha z.1 hk)
      (multilinearExp_coeff_nonneg (S z.1) (v z.1) (hv z.1 hk) (s z.1) (hs z.1 hk) z.2 hS)
  have hpoly (ω : Fin (L+1) → Bool) :
      poly Q c F (fun i ↦ bit (ω i))=
        ∑ k∈U, a k*Real.exp (s k*∑ b∈S k, v k b*monomial (E k b) ω) := by
    simp_rw [←multilinearExp_binary]
    simp only [poly,Q,c,F,Finset.sum_sigma,multilinearExp,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    apply Finset.sum_congr rfl
    intro R hR
    rw [mul_assoc]
    congr 2
    apply Finset.prod_congr
    · ext i; simp
    · intro i hi; rfl
  obtain ⟨ω,hbr,hcost⟩ := exists_combined_selection L Q c F hc T n t w hw p hp
  refine ⟨ω,hbr,?_⟩
  simpa only [hpoly] using hcost

end Erdos66MixedExponentialSelection
